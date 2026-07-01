"""
Project Name: Recon Tool
Developer: Lparc
Description: A script that can search the web and crawl a website for files and/or pages with specific names or text. The user will be able to filter for what to search. Will have a PyQt5 GUI
"""

import requests
from bs4 import BeautifulSoup
from urllib.parse import urljoin, urlparse
import re
from collections import deque
from typing import Set, List, Dict, Optional, Callable
import json
import csv
import asyncio
import aiohttp
from lxml import html as lxml_html
from urllib.robotparser import RobotFileParser
import hashlib
import time
import random
from datetime import datetime
import socket
import dns.resolver
import subprocess
import threading
from dataclasses import dataclass
from urllib.parse import quote
try:
    from simhash import Simhash
except ImportError:
    Simhash = None
try:
    from playwright.async_api import async_playwright
except ImportError:
    async_playwright = None
try:
    import whois
except ImportError:
    whois = None
from PyQt5.QtWidgets import (QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout, 
                             QTabWidget, QLabel, QLineEdit, QPushButton, QComboBox, 
                             QSpinBox, QCheckBox, QTextEdit, QTableWidget, QTableWidgetItem,
                             QHeaderView, QFileDialog, QMessageBox, QGroupBox, QSplitter,
                             QProgressBar, QFormLayout, QScrollArea)
from PyQt5.QtCore import Qt, QThread, pyqtSignal
from PyQt5.QtGui import QFont, QColor

class Crawler:
    def __init__(self, url: str, depth: int, 
                 use_async: bool = True,
                 use_js_rendering: bool = False,
                 respect_robots: bool = True,
                 polite_crawling: bool = True,
                 max_concurrent: int = 10,
                 rate_limit_delay: float = 1.0,
                 auth_credentials: Optional[Dict] = None):
        self.url = url
        self.depth = depth
        self.visited_urls: Set[str] = set()
        self.results: List[Dict] = []
        self.session = requests.Session()
        self.session.headers.update({
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36'
        })
        
        # Advanced features configuration
        self.use_async = use_async
        self.use_js_rendering = use_js_rendering
        self.respect_robots = respect_robots
        self.polite_crawling = polite_crawling
        self.max_concurrent = max_concurrent
        self.rate_limit_delay = rate_limit_delay
        self.auth_credentials = auth_credentials
        
        # Rate limiting and backoff
        self.domain_last_request: Dict[str, float] = {}
        self.domain_retry_count: Dict[str, int] = {}
        self.max_retries = 3
        
        # Robots.txt cache
        self.robots_cache: Dict[str, RobotFileParser] = {}
        
        # Content fingerprinting
        self.content_hashes: Dict[str, str] = {}
        self.near_duplicate_threshold = 0.85
        
        # Authentication
        if auth_credentials:
            self._setup_authentication()
        
        # Playwright browser (lazy initialization)
        self.playwright_browser = None
        self.playwright_context = None
    
    def _setup_authentication(self):
        """Setup authentication based on credentials."""
        if not self.auth_credentials:
            return
        
        auth_type = self.auth_credentials.get('type', 'basic')
        
        if auth_type == 'basic':
            self.session.auth = (
                self.auth_credentials.get('username', ''),
                self.auth_credentials.get('password', '')
            )
        elif auth_type == 'bearer':
            self.session.headers.update({
                'Authorization': f"Bearer {self.auth_credentials.get('token', '')}"
            })
        elif auth_type == 'session':
            # For session-based auth, we'll need to login first
            self.login_url = self.auth_credentials.get('login_url')
            self.login_data = self.auth_credentials.get('login_data', {})
    
    async def _perform_login(self, session: aiohttp.ClientSession) -> bool:
        """Perform login for session-based authentication."""
        if not hasattr(self, 'login_url') or not self.login_url:
            return True
        
        try:
            async with session.post(self.login_url, data=self.login_data) as response:
                return response.status == 200
        except Exception as e:
            print(f"Login failed: {e}")
            return False
    
    def _get_domain(self, url: str) -> str:
        """Extract domain from URL."""
        try:
            return urlparse(url).netloc
        except:
            return ''
    
    def _can_fetch(self, url: str) -> bool:
        """Check if URL can be fetched according to robots.txt."""
        if not self.respect_robots:
            return True
        
        domain = self._get_domain(url)
        if not domain:
            return True
        
        if domain not in self.robots_cache:
            robots_url = f"{urlparse(url).scheme}://{domain}/robots.txt"
            rp = RobotFileParser()
            rp.set_url(robots_url)
            try:
                rp.read()
            except:
                # If robots.txt is unavailable, allow crawling
                rp = None
            self.robots_cache[domain] = rp
        
        rp = self.robots_cache[domain]
        if rp is None:
            return True
        
        return rp.can_fetch(self.session.headers.get('User-Agent', '*'), url)
    
    def _get_crawl_delay(self, domain: str) -> float:
        """Get crawl delay from robots.txt or use default."""
        if domain in self.robots_cache and self.robots_cache[domain]:
            delay = self.robots_cache[domain].crawl_delay(self.session.headers.get('User-Agent', '*'))
            if delay is not None:
                return max(delay, self.rate_limit_delay)
        return self.rate_limit_delay
    
    def _apply_rate_limit(self, url: str):
        """Apply rate limiting with exponential backoff and jitter."""
        if not self.polite_crawling:
            return
        
        domain = self._get_domain(url)
        if not domain:
            return
        
        current_time = time.time()
        
        if domain in self.domain_last_request:
            elapsed = current_time - self.domain_last_request[domain]
            delay = self._get_crawl_delay(domain)
            
            if elapsed < delay:
                sleep_time = delay - elapsed
                # Add jitter (±20%)
                jitter = sleep_time * 0.2 * (random.random() * 2 - 1)
                time.sleep(max(0, sleep_time + jitter))
        
        self.domain_last_request[domain] = time.time()
    
    async def _async_apply_rate_limit(self, url: str):
        """Async version of rate limiting."""
        if not self.polite_crawling:
            return
        
        domain = self._get_domain(url)
        if not domain:
            return
        
        current_time = time.time()
        
        if domain in self.domain_last_request:
            elapsed = current_time - self.domain_last_request[domain]
            delay = self._get_crawl_delay(domain)
            
            if elapsed < delay:
                sleep_time = delay - elapsed
                jitter = sleep_time * 0.2 * (random.random() * 2 - 1)
                await asyncio.sleep(max(0, sleep_time + jitter))
        
        self.domain_last_request[domain] = time.time()
    
    def _compute_hash(self, content: str, algorithm: str = 'sha256') -> str:
        """Compute hash of content."""
        if algorithm == 'md5':
            return hashlib.md5(content.encode()).hexdigest()
        elif algorithm == 'sha256':
            return hashlib.sha256(content.encode()).hexdigest()
        return hashlib.sha256(content.encode()).hexdigest()
    
    def _is_near_duplicate(self, content: str) -> bool:
        """Check if content is near-duplicate using simhash."""
        if Simhash is None:
            return False
        
        content_hash = self._compute_hash(content)
        
        for existing_hash in self.content_hashes.values():
            # Simple hash comparison for now
            # For proper simhash, we'd need to implement shingling
            if content_hash == existing_hash:
                return True
        
        return False
    
    async def _render_with_playwright(self, url: str) -> Optional[str]:
        """Render page with Playwright for JavaScript content."""
        if async_playwright is None:
            return None
        
        try:
            if self.playwright_browser is None:
                playwright = await async_playwright().start()
                self.playwright_browser = await playwright.chromium.launch(headless=True)
                self.playwright_context = await self.playwright_browser.new_context()
            
            page = await self.playwright_context.new_page()
            await page.goto(url, wait_until='networkidle', timeout=30000)
            content = await page.content()
            await page.close()
            return content
        except Exception as e:
            print(f"Playwright rendering failed: {e}")
            return None
    
    async def _close_playwright(self):
        """Close Playwright browser."""
        if self.playwright_browser:
            await self.playwright_browser.close()
            self.playwright_browser = None
            self.playwright_context = None
        
    def is_valid_url(self, url: str) -> bool:
        """Check if URL is valid and belongs to the same domain."""
        try:
            parsed = urlparse(url)
            base_parsed = urlparse(self.url)
            return parsed.netloc == base_parsed.netloc and parsed.scheme in ['http', 'https']
        except:
            return False
    
    def normalize_url(self, url: str) -> str:
        """Normalize URL by removing fragments and ensuring consistent format."""
        parsed = urlparse(url)
        return parsed._replace(fragment='').geturl()
    
    def extract_links(self, soup: BeautifulSoup, base_url: str) -> List[str]:
        """Extract all links from the page using BeautifulSoup."""
        links = []
        for tag in soup.find_all(['a', 'link', 'script', 'img']):
            href = tag.get('href') or tag.get('src')
            if href:
                absolute_url = urljoin(base_url, href)
                if self.is_valid_url(absolute_url):
                    links.append(self.normalize_url(absolute_url))
        return links
    
    def extract_links_advanced(self, html_content: str, base_url: str) -> List[str]:
        """Extract links using lxml for advanced extraction (onclick, data-*, AJAX)."""
        links = []
        try:
            tree = lxml_html.fromstring(html_content)
            
            # Standard links
            for elem in tree.xpath('//a[@href]'):
                href = elem.get('href')
                if href:
                    absolute_url = urljoin(base_url, href)
                    if self.is_valid_url(absolute_url):
                        links.append(self.normalize_url(absolute_url))
            
            # Links from onclick attributes
            for elem in tree.xpath('//*[@onclick]'):
                onclick = elem.get('onclick')
                if onclick:
                    # Extract URLs from onclick JavaScript
                    url_pattern = r'(?:url\s*\(\s*["\']([^"\']+)["\']\s*\)|location\.href\s*=\s*["\']([^"\']+)["\']|window\.location\s*=\s*["\']([^"\']+)["\'])'
                    matches = re.findall(url_pattern, onclick, re.IGNORECASE)
                    for match in matches:
                        for url in match:
                            if url:
                                absolute_url = urljoin(base_url, url)
                                if self.is_valid_url(absolute_url):
                                    links.append(self.normalize_url(absolute_url))
            
            # Links from data-* attributes
            for attr in ['data-url', 'data-href', 'data-link', 'data-src', 'data-action']:
                for elem in tree.xpath(f'//*[@{attr}]'):
                    url = elem.get(attr)
                    if url:
                        absolute_url = urljoin(base_url, url)
                        if self.is_valid_url(absolute_url):
                            links.append(self.normalize_url(absolute_url))
            
            # AJAX calls in script tags
            for script in tree.xpath('//script'):
                script_content = script.text
                if script_content:
                    # Look for AJAX URLs
                    ajax_pattern = r'(?:url\s*:\s*["\']([^"\']+)["\']|\$\.get\s*\(\s*["\']([^"\']+)["\']|\$\.post\s*\(\s*["\']([^"\']+)["\']|fetch\s*\(\s*["\']([^"\']+)["\'])'
                    matches = re.findall(ajax_pattern, script_content, re.IGNORECASE)
                    for match in matches:
                        for url in match:
                            if url and not url.startswith('http') or url.startswith(base_url):
                                absolute_url = urljoin(base_url, url)
                                if self.is_valid_url(absolute_url):
                                    links.append(self.normalize_url(absolute_url))
            
            # Remove duplicates
            links = list(set(links))
            
        except Exception as e:
            print(f"Advanced link extraction failed: {e}")
            # Fallback to basic extraction
            soup = BeautifulSoup(html_content, 'html.parser')
            return self.extract_links(soup, base_url)
        
        return links
    
    def extract_text(self, soup: BeautifulSoup) -> str:
        """Extract visible text from the page."""
        for script in soup(['script', 'style', 'noscript']):
            script.decompose()
        return ' '.join(soup.stripped_strings)
    
    def search_in_content(self, content: str, search_terms: List[str], use_regex: bool = False) -> bool:
        """Search for terms in content."""
        if not search_terms:
            return True
        
        for term in search_terms:
            if use_regex:
                if re.search(term, content, re.IGNORECASE):
                    return True
            else:
                if term.lower() in content.lower():
                    return True
        return False
    
    def filter_by_extension(self, url: str, extensions: List[str]) -> bool:
        """Filter URLs by file extension."""
        if not extensions:
            return True
        parsed = urlparse(url)
        path = parsed.path.lower()
        return any(path.endswith(ext.lower()) for ext in extensions)
    
    async def _fetch_page_async(self, session: aiohttp.ClientSession, url: str) -> Optional[str]:
        """Fetch a single page asynchronously."""
        await self._async_apply_rate_limit(url)
        
        if not self._can_fetch(url):
            return None
        
        try:
            async with session.get(url, timeout=aiohttp.ClientTimeout(total=30)) as response:
                response.raise_for_status()
                return await response.text()
        except Exception as e:
            print(f"Error fetching {url}: {e}")
            return None
    
    async def _process_url_async(self, session: aiohttp.ClientSession, url: str, depth: int,
                                  search_text: Optional[List[str]], search_names: Optional[List[str]],
                                  file_extensions: Optional[List[str]], use_regex: bool,
                                  semaphore: asyncio.Semaphore) -> Optional[Dict]:
        """Process a single URL asynchronously."""
        async with semaphore:
            if url in self.visited_urls or depth > self.depth:
                return None
            
            self.visited_urls.add(url)
            
            html_content = await self._fetch_page_async(session, url)
            
            if html_content is None:
                return {
                    'url': url,
                    'depth': depth,
                    'type': 'error',
                    'error': 'Failed to fetch or blocked by robots.txt'
                }
            
            # Use JavaScript rendering if enabled
            if self.use_js_rendering:
                rendered_content = await self._render_with_playwright(url)
                if rendered_content:
                    html_content = rendered_content
            
            # Parse HTML
            soup = BeautifulSoup(html_content, 'html.parser')
            page_text = self.extract_text(soup)
            
            # Content fingerprinting
            content_hash = self._compute_hash(page_text)
            self.content_hashes[url] = content_hash
            
            if self._is_near_duplicate(page_text):
                return {
                    'url': url,
                    'depth': depth,
                    'type': 'duplicate',
                    'content_preview': 'Near-duplicate content'
                }
            
            # Check if page matches search criteria
            text_match = self.search_in_content(page_text, search_text, use_regex)
            name_match = self.search_in_content(url, search_names, use_regex)
            ext_match = self.filter_by_extension(url, file_extensions or [])
            
            result = None
            if text_match or name_match:
                result = {
                    'url': url,
                    'depth': depth,
                    'type': 'page',
                    'content_preview': page_text[:500] if page_text else '',
                    'matched_text': search_text if text_match else None,
                    'matched_name': search_names if name_match else None,
                    'content_hash': content_hash
                }
            
            return result
    
    async def crawl_async(self, 
                         search_text: Optional[List[str]] = None,
                         search_names: Optional[List[str]] = None,
                         file_extensions: Optional[List[str]] = None,
                         use_regex: bool = False,
                         progress_callback: Optional[Callable] = None) -> List[Dict]:
        """
        Crawl the website asynchronously using aiohttp.
        
        Args:
            search_text: List of text strings to search for in page content
            search_names: List of names to search for in URLs
            file_extensions: List of file extensions to filter
            use_regex: Whether to use regex for text matching
            progress_callback: Optional callback function for progress updates
            
        Returns:
            List of dictionaries containing crawl results
        """
        self.visited_urls.clear()
        self.results.clear()
        self.content_hashes.clear()
        
        # Create semaphore to limit concurrent requests
        semaphore = asyncio.Semaphore(self.max_concurrent)
        
        # Create aiohttp session
        connector = aiohttp.TCPConnector(limit=self.max_concurrent)
        async with aiohttp.ClientSession(connector=connector) as session:
            # Perform login if needed
            await self._perform_login(session)
            
            # BFS queue for URLs
            url_queue = asyncio.Queue()
            await url_queue.put((self.url, 0))
            
            # Track URLs to process
            urls_to_process = set([(self.url, 0)])
            
            while not url_queue.empty():
                # Get batch of URLs to process concurrently
                batch = []
                while not url_queue.empty() and len(batch) < self.max_concurrent:
                    try:
                        url, depth = await asyncio.wait_for(url_queue.get(), timeout=0.1)
                        batch.append((url, depth))
                    except asyncio.TimeoutError:
                        break
                
                if not batch:
                    break
                
                # Process batch concurrently
                tasks = []
                for url, depth in batch:
                    if depth <= self.depth:
                        task = self._process_url_async(
                            session, url, depth, search_text, search_names,
                            file_extensions, use_regex, semaphore
                        )
                        tasks.append(task)
                
                # Wait for all tasks in batch
                batch_results = await asyncio.gather(*tasks, return_exceptions=True)
                
                for result in batch_results:
                    if isinstance(result, Exception):
                        print(f"Task error: {result}")
                        continue
                    
                    if result and result.get('type') != 'error' and result.get('type') != 'duplicate':
                        self.results.append(result)
                        
                        # Extract links for further crawling
                        if result.get('depth') < self.depth:
                            html_content = await self._fetch_page_async(session, result['url'])
                            if html_content:
                                links = self.extract_links_advanced(html_content, result['url'])
                                for link in links:
                                    if link not in self.visited_urls:
                                        new_depth = result['depth'] + 1
                                        if (link, new_depth) not in urls_to_process:
                                            urls_to_process.add((link, new_depth))
                                            await url_queue.put((link, new_depth))
                    elif result:
                        self.results.append(result)
                
                if progress_callback:
                    progress_callback(len(self.visited_urls), len(self.results))
        
        # Close Playwright if used
        await self._close_playwright()
        
        return self.results
    
    def crawl(self, 
              search_text: Optional[List[str]] = None,
              search_names: Optional[List[str]] = None,
              file_extensions: Optional[List[str]] = None,
              use_regex: bool = False,
              progress_callback: Optional[Callable] = None) -> List[Dict]:
        """
        Crawl the website and search for matching content.
        Chooses between async and sync based on configuration.
        
        Args:
            search_text: List of text strings to search for in page content
            search_names: List of names to search for in URLs
            file_extensions: List of file extensions to filter (e.g., ['.pdf', '.doc'])
            use_regex: Whether to use regex for text matching
            progress_callback: Optional callback function for progress updates
            
        Returns:
            List of dictionaries containing crawl results
        """
        if self.use_async:
            # Run async crawl in event loop
            loop = asyncio.new_event_loop()
            asyncio.set_event_loop(loop)
            try:
                results = loop.run_until_complete(
                    self.crawl_async(search_text, search_names, file_extensions, use_regex, progress_callback)
                )
                return results
            finally:
                loop.close()
        else:
            return self.crawl_sync(search_text, search_names, file_extensions, use_regex, progress_callback)
    
    def crawl_sync(self, 
                   search_text: Optional[List[str]] = None,
                   search_names: Optional[List[str]] = None,
                   file_extensions: Optional[List[str]] = None,
                   use_regex: bool = False,
                   progress_callback: Optional[Callable] = None) -> List[Dict]:
        """
        Synchronous crawl with advanced features.
        
        Args:
            search_text: List of text strings to search for in page content
            search_names: List of names to search for in URLs
            file_extensions: List of file extensions to filter
            use_regex: Whether to use regex for text matching
            progress_callback: Optional callback function for progress updates
            
        Returns:
            List of dictionaries containing crawl results
        """
        self.visited_urls.clear()
        self.results.clear()
        self.content_hashes.clear()
        
        queue = deque([(self.url, 0)])
        
        while queue:
            current_url, current_depth = queue.popleft()
            
            if current_depth > self.depth or current_url in self.visited_urls:
                continue
            
            # Apply rate limiting
            self._apply_rate_limit(current_url)
            
            # Check robots.txt
            if not self._can_fetch(current_url):
                result = {
                    'url': current_url,
                    'depth': current_depth,
                    'type': 'error',
                    'error': 'Blocked by robots.txt'
                }
                self.results.append(result)
                continue
            
            self.visited_urls.add(current_url)
            
            try:
                response = self.session.get(current_url, timeout=10)
                response.raise_for_status()
                
                content_type = response.headers.get('content-type', '')
                
                if 'text/html' in content_type:
                    soup = BeautifulSoup(response.text, 'html.parser')
                    page_text = self.extract_text(soup)
                    
                    # Content fingerprinting
                    content_hash = self._compute_hash(page_text)
                    self.content_hashes[current_url] = content_hash
                    
                    if self._is_near_duplicate(page_text):
                        result = {
                            'url': current_url,
                            'depth': current_depth,
                            'type': 'duplicate',
                            'content_preview': 'Near-duplicate content'
                        }
                        self.results.append(result)
                        continue
                    
                    # Check if page matches search criteria
                    text_match = self.search_in_content(page_text, search_text, use_regex)
                    name_match = self.search_in_content(current_url, search_names, use_regex)
                    ext_match = self.filter_by_extension(current_url, file_extensions or [])
                    
                    if text_match or name_match:
                        result = {
                            'url': current_url,
                            'depth': current_depth,
                            'type': 'page',
                            'content_preview': page_text[:500] if page_text else '',
                            'matched_text': search_text if text_match else None,
                            'matched_name': search_names if name_match else None,
                            'content_hash': content_hash
                        }
                        self.results.append(result)
                    
                    # Extract links for further crawling
                    if current_depth < self.depth:
                        links = self.extract_links_advanced(response.text, current_url)
                        for link in links:
                            if link not in self.visited_urls:
                                queue.append((link, current_depth + 1))
                
                else:
                    # Non-HTML file
                    name_match = self.search_in_content(current_url, search_names, use_regex)
                    ext_match = self.filter_by_extension(current_url, file_extensions or [])
                    
                    if name_match or ext_match:
                        result = {
                            'url': current_url,
                            'depth': current_depth,
                            'type': 'file',
                            'content_type': content_type,
                            'matched_name': search_names if name_match else None,
                            'matched_extension': file_extensions if ext_match else None
                        }
                        self.results.append(result)
                
                if progress_callback:
                    progress_callback(len(self.visited_urls), len(self.results))
                    
            except requests.RequestException as e:
                result = {
                    'url': current_url,
                    'depth': current_depth,
                    'type': 'error',
                    'error': str(e)
                }
                self.results.append(result)
        
        return self.results
    
    def get_results(self) -> List[Dict]:
        """Return the crawl results."""
        return self.results
    
    def get_visited_urls(self) -> Set[str]:
        """Return the set of visited URLs."""
        return self.visited_urls
    
    def clear_results(self):
        """Clear previous crawl results."""
        self.visited_urls.clear()
        self.results.clear()

class Searcher:
    def __init__(self):
        self.session = requests.Session()
        self.session.headers.update({
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36'
        })
        self.results: List[Dict] = []
        self.search_engines = {
            'google': 'https://www.google.com/search',
            'bing': 'https://www.bing.com/search',
            'duckduckgo': 'https://duckduckgo.com/html/'
        }
    
    def search_google(self, query: str, num_results: int = 10, site: Optional[str] = None) -> List[Dict]:
        """Search using Google."""
        search_url = self.search_engines['google']
        params = {'q': query, 'num': num_results}
        if site:
            params['q'] = f"site:{site} {query}"
        
        try:
            response = self.session.get(search_url, params=params, timeout=10)
            response.raise_for_status()
            
            soup = BeautifulSoup(response.text, 'html.parser')
            results = []
            
            for div in soup.find_all('div', class_='g'):
                link_tag = div.find('a')
                if link_tag and link_tag.get('href'):
                    title_tag = div.find('h3')
                    snippet_tag = div.find('span', class_='st') or div.find('div', class_='st')
                    
                    result = {
                        'title': title_tag.get_text() if title_tag else '',
                        'url': link_tag.get('href'),
                        'snippet': snippet_tag.get_text() if snippet_tag else '',
                        'engine': 'google'
                    }
                    results.append(result)
            
            return results[:num_results]
            
        except requests.RequestException as e:
            return [{'error': str(e), 'engine': 'google'}]
    
    def search_bing(self, query: str, num_results: int = 10, site: Optional[str] = None) -> List[Dict]:
        """Search using Bing."""
        search_url = self.search_engines['bing']
        params = {'q': query, 'count': num_results}
        if site:
            params['q'] = f"site:{site} {query}"
        
        try:
            response = self.session.get(search_url, params=params, timeout=10)
            response.raise_for_status()
            
            soup = BeautifulSoup(response.text, 'html.parser')
            results = []
            
            for li in soup.find_all('li', class_='b_algo'):
                link_tag = li.find('a')
                if link_tag and link_tag.get('href'):
                    title_tag = link_tag.find('h2') or link_tag
                    snippet_tag = li.find('p')
                    
                    result = {
                        'title': title_tag.get_text() if title_tag else '',
                        'url': link_tag.get('href'),
                        'snippet': snippet_tag.get_text() if snippet_tag else '',
                        'engine': 'bing'
                    }
                    results.append(result)
            
            return results[:num_results]
            
        except requests.RequestException as e:
            return [{'error': str(e), 'engine': 'bing'}]
    
    def search_duckduckgo(self, query: str, num_results: int = 10, site: Optional[str] = None) -> List[Dict]:
        """Search using DuckDuckGo."""
        search_url = self.search_engines['duckduckgo']
        params = {'q': query}
        if site:
            params['q'] = f"site:{site} {query}"
        
        try:
            response = self.session.get(search_url, params=params, timeout=10)
            response.raise_for_status()
            
            soup = BeautifulSoup(response.text, 'html.parser')
            results = []
            
            for div in soup.find_all('div', class_='result'):
                link_tag = div.find('a', class_='result__a')
                if link_tag and link_tag.get('href'):
                    snippet_tag = div.find('a', class_='result__snippet')
                    
                    result = {
                        'title': link_tag.get_text(),
                        'url': link_tag.get('href'),
                        'snippet': snippet_tag.get_text() if snippet_tag else '',
                        'engine': 'duckduckgo'
                    }
                    results.append(result)
            
            return results[:num_results]
            
        except requests.RequestException as e:
            return [{'error': str(e), 'engine': 'duckduckgo'}]
    
    def search(self, 
               query: str, 
               engine: str = 'google',
               num_results: int = 10,
               site: Optional[str] = None,
               file_type: Optional[str] = None,
               exact_match: bool = False) -> List[Dict]:
        """
        Perform a web search using specified engine.
        
        Args:
            query: Search query string
            engine: Search engine to use ('google', 'bing', 'duckduckgo')
            num_results: Number of results to return
            site: Restrict search to specific domain
            file_type: Filter by file type (e.g., 'pdf', 'doc')
            exact_match: Use exact match (quotes around query)
            
        Returns:
            List of dictionaries containing search results
        """
        if exact_match:
            query = f'"{query}"'
        
        if file_type:
            query = f"{query} filetype:{file_type}"
        
        if engine == 'google':
            results = self.search_google(query, num_results, site)
        elif engine == 'bing':
            results = self.search_bing(query, num_results, site)
        elif engine == 'duckduckgo':
            results = self.search_duckduckgo(query, num_results, site)
        else:
            return [{'error': f'Unknown engine: {engine}'}]
        
        self.results = results
        return results
    
    def search_multiple_engines(self, 
                                query: str,
                                engines: List[str] = None,
                                num_results: int = 10,
                                site: Optional[str] = None,
                                file_type: Optional[str] = None,
                                exact_match: bool = False) -> Dict[str, List[Dict]]:
        """
        Search across multiple engines simultaneously.
        
        Args:
            query: Search query string
            engines: List of engines to search (default: all)
            num_results: Number of results per engine
            site: Restrict search to specific domain
            file_type: Filter by file type
            exact_match: Use exact match
            
        Returns:
            Dictionary mapping engine names to their results
        """
        if engines is None:
            engines = list(self.search_engines.keys())
        
        all_results = {}
        for engine in engines:
            all_results[engine] = self.search(
                query, engine, num_results, site, file_type, exact_match
            )
        
        return all_results
    
    def filter_results(self, 
                       results: List[Dict],
                       title_contains: Optional[str] = None,
                       url_contains: Optional[str] = None,
                       snippet_contains: Optional[str] = None) -> List[Dict]:
        """
        Filter search results by content criteria.
        
        Args:
            results: List of search results to filter
            title_contains: Filter by title content
            url_contains: Filter by URL content
            snippet_contains: Filter by snippet content
            
        Returns:
            Filtered list of results
        """
        filtered = []
        
        for result in results:
            if 'error' in result:
                continue
            
            match = True
            
            if title_contains and title_contains.lower() not in result.get('title', '').lower():
                match = False
            
            if url_contains and url_contains.lower() not in result.get('url', '').lower():
                match = False
            
            if snippet_contains and snippet_contains.lower() not in result.get('snippet', '').lower():
                match = False
            
            if match:
                filtered.append(result)
        
        return filtered
    
    def get_unique_domains(self, results: List[Dict]) -> Set[str]:
        """Extract unique domains from search results."""
        domains = set()
        for result in results:
            if 'url' in result:
                try:
                    parsed = urlparse(result['url'])
                    domains.add(parsed.netloc)
                except:
                    pass
        return domains
    
    def get_results(self) -> List[Dict]:
        """Return the most recent search results."""
        return self.results
    
    def clear_results(self):
        """Clear previous search results."""
        self.results.clear()

class Exporter:
    def __init__(self):
        self.supported_formats = ['json', 'csv', 'html', 'txt']
    
    def export_to_json(self, data: List[Dict], filepath: str) -> bool:
        """Export data to JSON format."""
        try:
            with open(filepath, 'w', encoding='utf-8') as f:
                json.dump(data, f, indent=2, ensure_ascii=False)
            return True
        except Exception as e:
            print(f"Error exporting to JSON: {e}")
            return False
    
    def export_to_csv(self, data: List[Dict], filepath: str) -> bool:
        """Export data to CSV format."""
        try:
            import csv
            if not data:
                return False
            
            fieldnames = set()
            for item in data:
                fieldnames.update(item.keys())
            fieldnames = list(fieldnames)
            
            with open(filepath, 'w', encoding='utf-8', newline='') as f:
                writer = csv.DictWriter(f, fieldnames=fieldnames)
                writer.writeheader()
                writer.writerows(data)
            return True
        except Exception as e:
            print(f"Error exporting to CSV: {e}")
            return False
    
    def export_to_html(self, data: List[Dict], filepath: str, title: str = "Recon Results") -> bool:
        """Export data to HTML format."""
        try:
            html_content = f"""<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>{title}</title>
    <style>
        body {{ font-family: Arial, sans-serif; margin: 20px; background-color: #f5f5f5; }}
        h1 {{ color: #333; }}
        table {{ border-collapse: collapse; width: 100%; background-color: white; box-shadow: 0 2px 4px rgba(0,0,0,0.1); }}
        th, td {{ border: 1px solid #ddd; padding: 12px; text-align: left; }}
        th {{ background-color: #4CAF50; color: white; }}
        tr:nth-child(even) {{ background-color: #f2f2f2; }}
        tr:hover {{ background-color: #ddd; }}
        .error {{ color: red; }}
        .page {{ color: blue; }}
        .file {{ color: green; }}
    </style>
</head>
<body>
    <h1>{title}</h1>
    <p>Total results: {len(data)}</p>
    <table>
"""
            
            if data:
                headers = set()
                for item in data:
                    headers.update(item.keys())
                headers = list(headers)
                
                html_content += "        <tr>\n"
                for header in headers:
                    html_content += f"            <th>{header}</th>\n"
                html_content += "        </tr>\n"
                
                for item in data:
                    row_class = ""
                    if item.get('type') == 'error':
                        row_class = ' class="error"'
                    elif item.get('type') == 'page':
                        row_class = ' class="page"'
                    elif item.get('type') == 'file':
                        row_class = ' class="file"'
                    
                    html_content += f"        <tr{row_class}>\n"
                    for header in headers:
                        value = item.get(header, '')
                        if header == 'url' and value:
                            value = f'<a href="{value}" target="_blank">{value}</a>'
                        html_content += f"            <td>{value}</td>\n"
                    html_content += "        </tr>\n"
            
            html_content += """    </table>
</body>
</html>"""
            
            with open(filepath, 'w', encoding='utf-8') as f:
                f.write(html_content)
            return True
        except Exception as e:
            print(f"Error exporting to HTML: {e}")
            return False
    
    def export_to_txt(self, data: List[Dict], filepath: str) -> bool:
        """Export data to plain text format."""
        try:
            with open(filepath, 'w', encoding='utf-8') as f:
                f.write(f"Total Results: {len(data)}\n")
                f.write("=" * 80 + "\n\n")
                
                for idx, item in enumerate(data, 1):
                    f.write(f"Result #{idx}\n")
                    f.write("-" * 40 + "\n")
                    for key, value in item.items():
                        f.write(f"{key}: {value}\n")
                    f.write("\n")
            return True
        except Exception as e:
            print(f"Error exporting to TXT: {e}")
            return False
    
    def export(self, data: List[Dict], filepath: str, format: str = 'json', title: str = "Recon Results") -> bool:
        """
        Export data to specified format.
        
        Args:
            data: List of dictionaries to export
            filepath: Output file path
            format: Export format ('json', 'csv', 'html', 'txt')
            title: Title for HTML export
            
        Returns:
            True if export successful, False otherwise
        """
        format = format.lower()
        
        if format not in self.supported_formats:
            print(f"Unsupported format: {format}. Supported formats: {', '.join(self.supported_formats)}")
            return False
        
        if format == 'json':
            return self.export_to_json(data, filepath)
        elif format == 'csv':
            return self.export_to_csv(data, filepath)
        elif format == 'html':
            return self.export_to_html(data, filepath, title)
        elif format == 'txt':
            return self.export_to_txt(data, filepath)
        
        return False
    
    def export_crawler_results(self, crawler: 'Crawler', filepath: str, format: str = 'json') -> bool:
        """Export crawler results to specified format."""
        return self.export(crawler.get_results(), filepath, format, "Crawler Results")
    
    def export_searcher_results(self, searcher: 'Searcher', filepath: str, format: str = 'json') -> bool:
        """Export searcher results to specified format."""
        return self.export(searcher.get_results(), filepath, format, "Search Results")

@dataclass
class SearchOperators:
    site: Optional[str] = None
    intitle: Optional[str] = None
    inurl: Optional[str] = None
    filetype: Optional[str] = None
    query: str = ""

class SearchOperatorParser:
    """Parse Google search operators from query strings."""
    
    OPERATORS = {
        'site:', 'intitle:', 'inurl:', 'filetype:', 'ext:', 'allintitle:', 
        'allinurl:', 'intext:', 'allintext:', 'cache:', 'link:', 'related:'
    }
    
    def __init__(self):
        self.pattern = re.compile(
            r'(?:site|intitle|inurl|filetype|ext|allint_title|allinurl|intext|allintext|cache|link|related):([^\s]+)',
            re.IGNORECASE
        )
    
    def parse(self, query: str) -> SearchOperators:
        """Parse search operators from query string."""
        operators = SearchOperators()
        operators.query = query
        
        # Parse site:
        site_match = re.search(r'site:([^\s]+)', query, re.IGNORECASE)
        if site_match:
            operators.site = site_match.group(1)
            operators.query = operators.query.replace(site_match.group(0), '').strip()
        
        # Parse intitle:
        intitle_match = re.search(r'intitle:([^\s]+)', query, re.IGNORECASE)
        if intitle_match:
            operators.intitle = intitle_match.group(1)
            operators.query = operators.query.replace(intitle_match.group(0), '').strip()
        
        # Parse inurl:
        inurl_match = re.search(r'inurl:([^\s]+)', query, re.IGNORECASE)
        if inurl_match:
            operators.inurl = inurl_match.group(1)
            operators.query = operators.query.replace(inurl_match.group(0), '').strip()
        
        # Parse filetype:
        filetype_match = re.search(r'filetype:([^\s]+)', query, re.IGNORECASE)
        if filetype_match:
            operators.filetype = filetype_match.group(1)
            operators.query = operators.query.replace(filetype_match.group(0), '').strip()
        
        return operators
    
    def build_query(self, operators: SearchOperators) -> str:
        """Build query string from SearchOperators object."""
        parts = []
        
        if operators.site:
            parts.append(f"site:{operators.site}")
        if operators.intitle:
            parts.append(f"intitle:{operators.intitle}")
        if operators.inurl:
            parts.append(f"inurl:{operators.inurl}")
        if operators.filetype:
            parts.append(f"filetype:{operators.filetype}")
        
        if operators.query:
            parts.append(operators.query)
        
        return ' '.join(parts)

class QueryExpander:
    """Intelligent query expansion using NLP techniques."""
    
    SYNONYM_MAP = {
        'hack': ['exploit', 'vulnerability', 'security flaw', 'breach', 'attack'],
        'password': ['credential', 'login', 'auth', 'authentication', 'pass'],
        'admin': ['administrator', 'root', 'dashboard', 'panel', 'console'],
        'login': ['signin', 'auth', 'authentication', 'portal', 'access'],
        'api': ['endpoint', 'rest', 'graphql', 'interface', 'service'],
        'database': ['db', 'sql', 'mysql', 'postgres', 'mongodb', 'data'],
        'server': ['host', 'machine', 'node', 'instance', 'backend'],
        'config': ['configuration', 'settings', 'setup', 'env', 'environment'],
        'secret': ['key', 'token', 'credential', 'password', 'private'],
        'upload': ['file', 'attachment', 'document', 'image', 'media'],
        'error': ['exception', 'fail', 'bug', 'issue', 'problem'],
        'test': ['demo', 'staging', 'dev', 'development', 'sandbox']
    }
    
    def __init__(self):
        self.synonym_map = self.SYNONYM_MAP
    
    def expand_synonyms(self, query: str, max_synonyms: int = 2) -> List[str]:
        """Expand query using synonyms."""
        words = query.lower().split()
        expanded_queries = [query]
        
        for word in words:
            if word in self.synonym_map:
                synonyms = self.synonym_map[word][:max_synonyms]
                for synonym in synonyms:
                    new_query = query.replace(word, synonym, 1)
                    expanded_queries.append(new_query)
        
        return list(set(expanded_queries))
    
    def expand_with_variations(self, query: str) -> List[str]:
        """Add common variations to query."""
        variations = [query]
        
        # Add quotes for exact match
        if not query.startswith('"'):
            variations.append(f'"{query}"')
        
        # Add wildcard variations
        words = query.split()
        if len(words) > 1:
            variations.append(' '.join([words[0], '*'] + words[1:]))
        
        # Add OR variations
        if len(words) > 1:
            variations.append(' OR '.join(words))
        
        return list(set(variations))
    
    def expand_query(self, query: str, use_synonyms: bool = True, 
                     use_variations: bool = True) -> List[str]:
        """Comprehensive query expansion."""
        expanded = [query]
        
        if use_synonyms:
            expanded.extend(self.expand_synonyms(query))
        
        if use_variations:
            expanded.extend(self.expand_with_variations(query))
        
        return list(set(expanded))

class MultiEngineAggregator:
    """Aggregate and deduplicate results from multiple search engines."""
    
    def __init__(self):
        self.searcher = Searcher()
        self.query_expander = QueryExpander()
    
    def search_all(self, query: str, num_results: int = 10, 
                   expand_query: bool = False) -> List[Dict]:
        """Search across all engines and aggregate results."""
        queries = [query]
        
        if expand_query:
            queries = self.query_expander.expand_query(query)
        
        all_results = []
        
        for q in queries:
            # Search all engines
            engine_results = self.searcher.search_multiple_engines(
                q, 
                engines=['google', 'bing', 'duckduckgo'],
                num_results=num_results
            )
            
            for engine, results in engine_results.items():
                for result in results:
                    if 'error' not in result:
                        result['original_query'] = q
                        result['search_engine'] = engine
                        all_results.append(result)
        
        # Deduplicate by URL
        seen_urls = set()
        unique_results = []
        
        for result in all_results:
            url = result.get('url', '')
            if url and url not in seen_urls:
                seen_urls.add(url)
                unique_results.append(result)
        
        # Rank by relevance (simple scoring based on title/snippet match)
        ranked_results = self._rank_results(unique_results, query)
        
        return ranked_results[:num_results * 3]  # Return more results for aggregation
    
    def _rank_results(self, results: List[Dict], query: str) -> List[Dict]:
        """Rank results by relevance score."""
        query_words = set(query.lower().split())
        
        for result in results:
            score = 0
            title = result.get('title', '').lower()
            snippet = result.get('snippet', '').lower()
            
            # Score based on word matches in title
            for word in query_words:
                if word in title:
                    score += 3
                if word in snippet:
                    score += 1
            
            result['relevance_score'] = score
        
        # Sort by score descending
        return sorted(results, key=lambda x: x.get('relevance_score', 0), reverse=True)
    
    def merge_results(self, results_dict: Dict[str, List[Dict]]) -> List[Dict]:
        """Merge results from multiple engines."""
        merged = []
        seen_urls = set()
        
        for engine, results in results_dict.items():
            for result in results:
                url = result.get('url', '')
                if url and url not in seen_urls:
                    seen_urls.add(url)
                    result['engines'] = [engine]
                    merged.append(result)
                elif url in seen_urls:
                    # Add engine to existing result
                    for existing in merged:
                        if existing.get('url') == url:
                            if engine not in existing.get('engines', []):
                                existing['engines'] = existing.get('engines', []) + [engine]
                            break
        
        return merged

class SubdomainDiscovery:
    """Discover subdomains using DNS brute-force and Certificate Transparency logs."""
    
    COMMON_SUBDOMAINS = [
        'www', 'mail', 'ftp', 'admin', 'blog', 'api', 'dev', 'staging', 'test',
        'app', 'portal', 'secure', 'vpn', 'cdn', 'static', 'assets', 'img',
        'shop', 'store', 'support', 'help', 'docs', 'wiki', 'forum', 'community',
        'm', 'mobile', 'beta', 'alpha', 'demo', 'sandbox', 'lab', 'internal',
        'dashboard', 'panel', 'console', 'manage', 'cp', 'webmail', 'email',
        'ns1', 'ns2', 'dns', 'mx', 'smtp', 'pop', 'imap', 'webdisk', 'cpanel',
        'whm', 'autodiscover', 'autoconfig', 'wp', 'joomla', 'drupal', 'magento'
    ]
    
    def __init__(self):
        self.resolver = dns.resolver.Resolver()
        self.resolver.timeout = 2
        self.resolver.lifetime = 2
    
    def dns_brute_force(self, domain: str, wordlist: Optional[List[str]] = None,
                        progress_callback: Optional[Callable] = None) -> Set[str]:
        """Brute force subdomains using DNS lookups."""
        if wordlist is None:
            wordlist = self.COMMON_SUBDOMAINS
        
        found_subdomains = set()
        total = len(wordlist)
        
        for idx, subdomain in enumerate(wordlist):
            full_domain = f"{subdomain}.{domain}"
            
            try:
                # Try A record
                self.resolver.resolve(full_domain, 'A')
                found_subdomains.add(full_domain)
            except:
                pass
            
            try:
                # Try CNAME record
                self.resolver.resolve(full_domain, 'CNAME')
                found_subdomains.add(full_domain)
            except:
                pass
            
            if progress_callback:
                progress_callback(idx + 1, total, len(found_subdomains))
        
        return found_subdomains
    
    def query_crtsh(self, domain: str) -> Set[str]:
        """Query crt.sh for certificate transparency logs."""
        subdomains = set()
        
        try:
            url = f"https://crt.sh/?q=%.{domain}&output=json"
            response = requests.get(url, timeout=10)
            response.raise_for_status()
            
            data = response.json()
            
            for entry in data:
                name_value = entry.get('name_value', '')
                for name in name_value.split('\n'):
                    name = name.strip()
                    if domain in name:
                        subdomains.add(name)
        
        except Exception as e:
            print(f"Error querying crt.sh: {e}")
        
        return subdomains
    
    def discover_subdomains(self, domain: str, use_dns_brute: bool = True,
                           use_crtsh: bool = True, wordlist: Optional[List[str]] = None,
                           progress_callback: Optional[Callable] = None) -> Dict[str, Set[str]]:
        """Discover subdomains using multiple methods."""
        results = {}
        
        if use_dns_brute:
            results['dns_brute_force'] = self.dns_brute_force(domain, wordlist, progress_callback)
        
        if use_crtsh:
            results['certificate_transparency'] = self.query_crtsh(domain)
        
        # Merge all results
        all_subdomains = set()
        for method, subdomains in results.items():
            all_subdomains.update(subdomains)
        
        results['all'] = all_subdomains
        
        return results

class TorCrawler:
    """Crawl .onion services through Tor SOCKS5 proxy."""
    
    def __init__(self, proxy_host: str = '127.0.0.1', proxy_port: int = 9050):
        self.proxy_host = proxy_host
        self.proxy_port = proxy_port
        self.session = requests.Session()
        self.session.headers.update({
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
        })
    
    def configure_proxy(self):
        """Configure session to use Tor SOCKS5 proxy."""
        self.session.proxies = {
            'http': f'socks5h://{self.proxy_host}:{self.proxy_port}',
            'https': f'socks5h://{self.proxy_host}:{self.proxy_port}'
        }
    
    def crawl_onion(self, onion_url: str, depth: int = 2) -> List[Dict]:
        """Crawl .onion service through Tor."""
        self.configure_proxy()
        
        crawler = Crawler(onion_url, depth, use_async=False)
        crawler.session = self.session
        
        try:
            results = crawler.crawl()
            return results
        except Exception as e:
            return [{'error': str(e), 'url': onion_url}]
    
    def check_tor_connection(self) -> bool:
        """Check if Tor connection is working."""
        self.configure_proxy()
        
        try:
            response = self.session.get('https://check.torproject.org', timeout=10)
            return 'Congratulations' in response.text
        except:
            return False

class WhoIsSearch:
    """Perform WhoIs lookups on domains."""
    
    def __init__(self):
        self.cache = {}
    
    def lookup(self, domain: str) -> Dict:
        """Perform WhoIs lookup for domain."""
        if whois is None:
            return {'error': 'python-whois library not installed'}
        
        if domain in self.cache:
            return self.cache[domain]
        
        try:
            domain_info = whois.whois(domain)
            
            result = {
                'domain_name': domain_info.domain_name,
                'registrar': domain_info.registrar,
                'creation_date': str(domain_info.creation_date) if domain_info.creation_date else None,
                'expiration_date': str(domain_info.expiration_date) if domain_info.expiration_date else None,
                'updated_date': str(domain_info.updated_date) if domain_info.updated_date else None,
                'name_servers': domain_info.name_servers,
                'status': domain_info.status,
                'emails': domain_info.emails,
                'org': domain_info.org,
                'country': domain_info.country
            }
            
            self.cache[domain] = result
            return result
        
        except Exception as e:
            return {'error': str(e), 'domain': domain}
    
    def batch_lookup(self, domains: List[str]) -> Dict[str, Dict]:
        """Perform WhoIs lookup for multiple domains."""
        results = {}
        
        for domain in domains:
            results[domain] = self.lookup(domain)
        
        return results

class PortScanner:
    """Nmap-style port scanner."""
    
    COMMON_PORTS = {
        21: 'FTP',
        22: 'SSH',
        23: 'Telnet',
        25: 'SMTP',
        53: 'DNS',
        80: 'HTTP',
        110: 'POP3',
        143: 'IMAP',
        443: 'HTTPS',
        445: 'SMB',
        993: 'IMAPS',
        995: 'POP3S',
        3306: 'MySQL',
        3389: 'RDP',
        5432: 'PostgreSQL',
        5900: 'VNC',
        6379: 'Redis',
        8080: 'HTTP-Proxy',
        8443: 'HTTPS-Alt',
        8888: 'HTTP-Alt',
        9200: 'Elasticsearch'
    }
    
    def __init__(self, timeout: float = 1.0):
        self.timeout = timeout
    
    def scan_port(self, host: str, port: int) -> Dict:
        """Scan a single port."""
        result = {
            'host': host,
            'port': port,
            'service': self.COMMON_PORTS.get(port, 'unknown'),
            'status': 'closed',
            'error': None
        }
        
        try:
            sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            sock.settimeout(self.timeout)
            
            result_code = sock.connect_ex((host, port))
            
            if result_code == 0:
                result['status'] = 'open'
            
            sock.close()
        
        except Exception as e:
            result['error'] = str(e)
            result['status'] = 'error'
        
        return result
    
    def scan_ports(self, host: str, ports: Optional[List[int]] = None,
                   progress_callback: Optional[Callable] = None) -> List[Dict]:
        """Scan multiple ports on a host."""
        if ports is None:
            ports = list(self.COMMON_PORTS.keys())
        
        results = []
        total = len(ports)
        
        for idx, port in enumerate(ports):
            result = self.scan_port(host, port)
            results.append(result)
            
            if progress_callback:
                progress_callback(idx + 1, total, len([r for r in results if r['status'] == 'open']))
        
        return results
    
    def scan_range(self, host: str, start_port: int, end_port: int,
                   progress_callback: Optional[Callable] = None) -> List[Dict]:
        """Scan a range of ports."""
        ports = list(range(start_port, end_port + 1))
        return self.scan_ports(host, ports, progress_callback)
    
    def async_scan_ports(self, host: str, ports: Optional[List[int]] = None,
                         max_threads: int = 50) -> List[Dict]:
        """Scan ports asynchronously using threads."""
        if ports is None:
            ports = list(self.COMMON_PORTS.keys())
        
        results = [None] * len(ports)
        threads = []
        
        def scan_worker(idx, port):
            results[idx] = self.scan_port(host, port)
        
        for idx, port in enumerate(ports):
            thread = threading.Thread(target=scan_worker, args=(idx, port))
            threads.append(thread)
            thread.start()
            
            if len(threads) >= max_threads:
                for t in threads:
                    t.join()
                threads = []
        
        for thread in threads:
            thread.join()
        
        return [r for r in results if r is not None]

class SearchWorker(QThread):
    progress = pyqtSignal(str)
    finished = pyqtSignal(list)
    error = pyqtSignal(str)
    
    def __init__(self, searcher, query, engine, num_results, site, file_type, exact_match):
        super().__init__()
        self.searcher = searcher
        self.query = query
        self.engine = engine
        self.num_results = num_results
        self.site = site
        self.file_type = file_type
        self.exact_match = exact_match
    
    def run(self):
        try:
            self.progress.emit(f"Searching '{self.query}' on {self.engine}...")
            results = self.searcher.search(
                self.query, self.engine, self.num_results, 
                self.site, self.file_type, self.exact_match
            )
            self.progress.emit(f"Found {len(results)} results")
            self.finished.emit(results)
        except Exception as e:
            self.error.emit(str(e))

class CrawlWorker(QThread):
    progress = pyqtSignal(str)
    finished = pyqtSignal(list)
    error = pyqtSignal(str)
    
    def __init__(self, crawler, search_text, search_names, file_extensions, use_regex,
                 use_async=True, use_js_rendering=False, respect_robots=True, 
                 polite_crawling=True, max_concurrent=10, rate_limit_delay=1.0,
                 auth_credentials=None):
        super().__init__()
        self.crawler = crawler
        self.search_text = search_text
        self.search_names = search_names
        self.file_extensions = file_extensions
        self.use_regex = use_regex
        self.use_async = use_async
        self.use_js_rendering = use_js_rendering
        self.respect_robots = respect_robots
        self.polite_crawling = polite_crawling
        self.max_concurrent = max_concurrent
        self.rate_limit_delay = rate_limit_delay
        self.auth_credentials = auth_credentials
    
    def run(self):
        try:
            self.progress.emit("Starting crawl...")
            
            # Update crawler configuration
            self.crawler.use_async = self.use_async
            self.crawler.use_js_rendering = self.use_js_rendering
            self.crawler.respect_robots = self.respect_robots
            self.crawler.polite_crawling = self.polite_crawling
            self.crawler.max_concurrent = self.max_concurrent
            self.crawler.rate_limit_delay = self.rate_limit_delay
            self.crawler.auth_credentials = self.auth_credentials
            
            results = self.crawler.crawl(
                search_text=self.search_text,
                search_names=self.search_names,
                file_extensions=self.file_extensions,
                use_regex=self.use_regex,
                progress_callback=lambda v, r: self.progress.emit(f"Visited: {v}, Found: {r}")
            )
            self.progress.emit(f"Crawl complete. Found {len(results)} results")
            self.finished.emit(results)
        except Exception as e:
            self.error.emit(str(e))

class GUI(QMainWindow):
    def __init__(self):
        super().__init__()
        self.searcher = Searcher()
        self.crawler = None
        self.exporter = Exporter()
        self.current_results = []
        
        # New feature instances
        self.operator_parser = SearchOperatorParser()
        self.query_expander = QueryExpander()
        self.multi_engine_aggregator = MultiEngineAggregator()
        self.subdomain_discovery = SubdomainDiscovery()
        self.tor_crawler = TorCrawler()
        self.whois_search = WhoIsSearch()
        self.port_scanner = PortScanner()
        
        self.init_ui()
    
    def init_ui(self):
        self.setWindowTitle("Recon Tool - Advanced Web Reconnaissance")
        self.setGeometry(100, 100, 1400, 900)
        
        # Central widget
        central_widget = QWidget()
        self.setCentralWidget(central_widget)
        
        # Main layout
        main_layout = QVBoxLayout(central_widget)
        
        # Tab widget
        self.tab_widget = QTabWidget()
        main_layout.addWidget(self.tab_widget)
        
        # Create tabs
        self.create_search_tab()
        self.create_crawl_tab()
        self.create_advanced_search_tab()
        self.create_multi_engine_tab()
        self.create_subdomain_tab()
        self.create_tor_tab()
        self.create_whois_tab()
        self.create_port_scanner_tab()
        
        # Status bar
        self.status_label = QLabel("Ready")
        self.statusBar().addWidget(self.status_label)
    
    def create_search_tab(self):
        search_tab = QWidget()
        layout = QVBoxLayout(search_tab)
        
        # Search configuration group
        config_group = QGroupBox("Search Configuration")
        config_layout = QFormLayout()
        
        self.search_query = QLineEdit()
        self.search_query.setPlaceholderText("Enter search query...")
        config_layout.addRow("Query:", self.search_query)
        
        self.search_engine = QComboBox()
        self.search_engine.addItems(['google', 'bing', 'duckduckgo'])
        config_layout.addRow("Engine:", self.search_engine)
        
        self.num_results = QSpinBox()
        self.num_results.setRange(1, 100)
        self.num_results.setValue(10)
        config_layout.addRow("Results:", self.num_results)
        
        self.site_filter = QLineEdit()
        self.site_filter.setPlaceholderText("e.g., example.com (optional)")
        config_layout.addRow("Site Filter:", self.site_filter)
        
        self.file_type = QLineEdit()
        self.file_type.setPlaceholderText("e.g., pdf (optional)")
        config_layout.addRow("File Type:", self.file_type)
        
        self.exact_match = QCheckBox("Exact Match")
        config_layout.addRow("", self.exact_match)
        
        config_group.setLayout(config_layout)
        layout.addWidget(config_group)
        
        # Search button
        search_btn = QPushButton("Search")
        search_btn.clicked.connect(self.perform_search)
        layout.addWidget(search_btn)
        
        # Progress bar
        self.search_progress = QProgressBar()
        self.search_progress.setVisible(False)
        layout.addWidget(self.search_progress)
        
        # Results table
        self.search_results_table = QTableWidget()
        self.search_results_table.setColumnCount(4)
        self.search_results_table.setHorizontalHeaderLabels(['Title', 'URL', 'Snippet', 'Engine'])
        self.search_results_table.horizontalHeader().setSectionResizeMode(QHeaderView.Stretch)
        self.search_results_table.setSelectionBehavior(QTableWidget.SelectRows)
        self.search_results_table.setEditTriggers(QTableWidget.NoEditTriggers)
        layout.addWidget(self.search_results_table)
        
        # Export buttons
        export_layout = QHBoxLayout()
        export_layout.addWidget(QLabel("Export:"))
        
        for fmt in ['JSON', 'CSV', 'HTML', 'TXT']:
            btn = QPushButton(fmt)
            btn.clicked.connect(lambda checked, f=fmt: self.export_search_results(f.lower()))
            export_layout.addWidget(btn)
        
        export_layout.addStretch()
        layout.addLayout(export_layout)
        
        self.tab_widget.addTab(search_tab, "Search")
    
    def create_crawl_tab(self):
        crawl_tab = QWidget()
        layout = QVBoxLayout(crawl_tab)
        
        # Crawler configuration group
        config_group = QGroupBox("Crawler Configuration")
        config_layout = QFormLayout()
        
        self.crawl_url = QLineEdit()
        self.crawl_url.setPlaceholderText("Enter URL to crawl...")
        config_layout.addRow("URL:", self.crawl_url)
        
        self.crawl_depth = QSpinBox()
        self.crawl_depth.setRange(1, 10)
        self.crawl_depth.setValue(2)
        config_layout.addRow("Depth:", self.crawl_depth)
        
        self.search_text = QLineEdit()
        self.search_text.setPlaceholderText("Comma-separated text to search (optional)")
        config_layout.addRow("Search Text:", self.search_text)
        
        self.search_names = QLineEdit()
        self.search_names.setPlaceholderText("Comma-separated names in URLs (optional)")
        config_layout.addRow("Search Names:", self.search_names)
        
        self.file_extensions = QLineEdit()
        self.file_extensions.setPlaceholderText("Comma-separated extensions (e.g., .pdf,.doc)")
        config_layout.addRow("File Extensions:", self.file_extensions)
        
        self.use_regex = QCheckBox("Use Regex")
        config_layout.addRow("", self.use_regex)
        
        config_group.setLayout(config_layout)
        layout.addWidget(config_group)
        
        # Advanced features group
        advanced_group = QGroupBox("Advanced Features")
        advanced_layout = QFormLayout()
        
        self.use_async = QCheckBox("Enable Async Crawling")
        self.use_async.setChecked(True)
        advanced_layout.addRow("", self.use_async)
        
        self.use_js_rendering = QCheckBox("Enable JavaScript Rendering (Playwright)")
        self.use_js_rendering.setChecked(False)
        advanced_layout.addRow("", self.use_js_rendering)
        
        self.respect_robots = QCheckBox("Respect robots.txt")
        self.respect_robots.setChecked(True)
        advanced_layout.addRow("", self.respect_robots)
        
        self.polite_crawling = QCheckBox("Enable Polite Crawling (Rate Limiting)")
        self.polite_crawling.setChecked(True)
        advanced_layout.addRow("", self.polite_crawling)
        
        self.max_concurrent = QSpinBox()
        self.max_concurrent.setRange(1, 50)
        self.max_concurrent.setValue(10)
        advanced_layout.addRow("Max Concurrent Requests:", self.max_concurrent)
        
        self.rate_limit_delay = QSpinBox()
        self.rate_limit_delay.setRange(0, 10)
        self.rate_limit_delay.setSingleStep(0.5)
        self.rate_limit_delay.setValue(1.0)
        advanced_layout.addRow("Rate Limit Delay (s):", self.rate_limit_delay)
        
        self.auth_type = QComboBox()
        self.auth_type.addItems(['None', 'Basic Auth', 'Bearer Token', 'Session-based'])
        advanced_layout.addRow("Authentication:", self.auth_type)
        
        self.auth_username = QLineEdit()
        self.auth_username.setPlaceholderText("Username (for Basic Auth)")
        advanced_layout.addRow("Username:", self.auth_username)
        
        self.auth_password = QLineEdit()
        self.auth_password.setPlaceholderText("Password (for Basic Auth)")
        self.auth_password.setEchoMode(QLineEdit.Password)
        advanced_layout.addRow("Password:", self.auth_password)
        
        self.auth_token = QLineEdit()
        self.auth_token.setPlaceholderText("Token (for Bearer Auth)")
        advanced_layout.addRow("Token:", self.auth_token)
        
        self.login_url = QLineEdit()
        self.login_url.setPlaceholderText("Login URL (for Session-based)")
        advanced_layout.addRow("Login URL:", self.login_url)
        
        advanced_group.setLayout(advanced_layout)
        layout.addWidget(advanced_group)
        
        # Crawl button
        crawl_btn = QPushButton("Start Crawl")
        crawl_btn.clicked.connect(self.perform_crawl)
        layout.addWidget(crawl_btn)
        
        # Progress bar
        self.crawl_progress = QProgressBar()
        self.crawl_progress.setVisible(False)
        layout.addWidget(self.crawl_progress)
        
        # Results table
        self.crawl_results_table = QTableWidget()
        self.crawl_results_table.setColumnCount(5)
        self.crawl_results_table.setHorizontalHeaderLabels(['URL', 'Type', 'Depth', 'Match Info', 'Preview/Error'])
        self.crawl_results_table.horizontalHeader().setSectionResizeMode(QHeaderView.Stretch)
        self.crawl_results_table.setSelectionBehavior(QTableWidget.SelectRows)
        self.crawl_results_table.setEditTriggers(QTableWidget.NoEditTriggers)
        layout.addWidget(self.crawl_results_table)
        
        # Export buttons
        export_layout = QHBoxLayout()
        export_layout.addWidget(QLabel("Export:"))
        
        for fmt in ['JSON', 'CSV', 'HTML', 'TXT']:
            btn = QPushButton(fmt)
            btn.clicked.connect(lambda checked, f=fmt: self.export_crawl_results(f.lower()))
            export_layout.addWidget(btn)
        
        export_layout.addStretch()
        layout.addLayout(export_layout)
        
        self.tab_widget.addTab(crawl_tab, "Crawl")
    
    def create_advanced_search_tab(self):
        """Create tab for advanced search with operator parsing."""
        advanced_tab = QWidget()
        layout = QVBoxLayout(advanced_tab)
        
        # Operator parsing group
        operator_group = QGroupBox("Search Operator Parser")
        operator_layout = QFormLayout()
        
        self.advanced_query = QLineEdit()
        self.advanced_query.setPlaceholderText("Enter query with operators (e.g., 'site:example.com intitle:admin')")
        operator_layout.addRow("Query:", self.advanced_query)
        
        parse_btn = QPushButton("Parse Operators")
        parse_btn.clicked.connect(self.parse_operators)
        operator_layout.addRow("", parse_btn)
        
        self.parsed_operators = QTextEdit()
        self.parsed_operators.setReadOnly(True)
        self.parsed_operators.setMaximumHeight(100)
        operator_layout.addRow("Parsed:", self.parsed_operators)
        
        operator_group.setLayout(operator_layout)
        layout.addWidget(operator_group)
        
        # Query expansion group
        expansion_group = QGroupBox("Query Expansion")
        expansion_layout = QFormLayout()
        
        self.expand_query_input = QLineEdit()
        self.expand_query_input.setPlaceholderText("Enter query to expand")
        expansion_layout.addRow("Query:", self.expand_query_input)
        
        self.use_synonyms = QCheckBox("Use Synonyms")
        self.use_synonyms.setChecked(True)
        expansion_layout.addRow("", self.use_synonyms)
        
        self.use_variations = QCheckBox("Use Variations")
        self.use_variations.setChecked(True)
        expansion_layout.addRow("", self.use_variations)
        
        expand_btn = QPushButton("Expand Query")
        expand_btn.clicked.connect(self.expand_query)
        expansion_layout.addRow("", expand_btn)
        
        self.expanded_queries = QTextEdit()
        self.expanded_queries.setReadOnly(True)
        self.expanded_queries.setMaximumHeight(150)
        expansion_layout.addRow("Expanded:", self.expanded_queries)
        
        expansion_group.setLayout(expansion_layout)
        layout.addWidget(expansion_group)
        
        self.tab_widget.addTab(advanced_tab, "Advanced Search")
    
    def create_multi_engine_tab(self):
        """Create tab for multi-engine search aggregation."""
        multi_tab = QWidget()
        layout = QVBoxLayout(multi_tab)
        
        # Multi-engine search group
        search_group = QGroupBox("Multi-Engine Search")
        search_layout = QFormLayout()
        
        self.multi_query = QLineEdit()
        self.multi_query.setPlaceholderText("Enter search query")
        search_layout.addRow("Query:", self.multi_query)
        
        self.multi_num_results = QSpinBox()
        self.multi_num_results.setRange(1, 50)
        self.multi_num_results.setValue(10)
        search_layout.addRow("Results per Engine:", self.multi_num_results)
        
        self.expand_multi_query = QCheckBox("Expand Query")
        search_layout.addRow("", self.expand_multi_query)
        
        multi_search_btn = QPushButton("Search All Engines")
        multi_search_btn.clicked.connect(self.perform_multi_engine_search)
        search_layout.addRow("", multi_search_btn)
        
        search_group.setLayout(search_layout)
        layout.addWidget(search_group)
        
        # Progress bar
        self.multi_progress = QProgressBar()
        self.multi_progress.setVisible(False)
        layout.addWidget(self.multi_progress)
        
        # Results table
        self.multi_results_table = QTableWidget()
        self.multi_results_table.setColumnCount(5)
        self.multi_results_table.setHorizontalHeaderLabels(['Title', 'URL', 'Snippet', 'Engine', 'Score'])
        self.multi_results_table.horizontalHeader().setSectionResizeMode(QHeaderView.Stretch)
        self.multi_results_table.setSelectionBehavior(QTableWidget.SelectRows)
        self.multi_results_table.setEditTriggers(QTableWidget.NoEditTriggers)
        layout.addWidget(self.multi_results_table)
        
        # Export buttons
        export_layout = QHBoxLayout()
        export_layout.addWidget(QLabel("Export:"))
        
        for fmt in ['JSON', 'CSV', 'HTML', 'TXT']:
            btn = QPushButton(fmt)
            btn.clicked.connect(lambda checked, f=fmt: self.export_multi_results(f.lower()))
            export_layout.addWidget(btn)
        
        export_layout.addStretch()
        layout.addLayout(export_layout)
        
        self.tab_widget.addTab(multi_tab, "Multi-Engine")
    
    def create_subdomain_tab(self):
        """Create tab for subdomain discovery."""
        subdomain_tab = QWidget()
        layout = QVBoxLayout(subdomain_tab)
        
        # Subdomain discovery group
        discovery_group = QGroupBox("Subdomain Discovery")
        discovery_layout = QFormLayout()
        
        self.subdomain_domain = QLineEdit()
        self.subdomain_domain.setPlaceholderText("Enter domain (e.g., example.com)")
        discovery_layout.addRow("Domain:", self.subdomain_domain)
        
        self.use_dns_brute = QCheckBox("DNS Brute Force")
        self.use_dns_brute.setChecked(True)
        discovery_layout.addRow("", self.use_dns_brute)
        
        self.use_crtsh = QCheckBox("Certificate Transparency (crt.sh)")
        self.use_crtsh.setChecked(True)
        discovery_layout.addRow("", self.use_crtsh)
        
        discover_btn = QPushButton("Discover Subdomains")
        discover_btn.clicked.connect(self.perform_subdomain_discovery)
        discovery_layout.addRow("", discover_btn)
        
        discovery_group.setLayout(discovery_layout)
        layout.addWidget(discovery_group)
        
        # Progress bar
        self.subdomain_progress = QProgressBar()
        self.subdomain_progress.setVisible(False)
        layout.addWidget(self.subdomain_progress)
        
        # Results table
        self.subdomain_results_table = QTableWidget()
        self.subdomain_results_table.setColumnCount(3)
        self.subdomain_results_table.setHorizontalHeaderLabels(['Subdomain', 'Method', 'Status'])
        self.subdomain_results_table.horizontalHeader().setSectionResizeMode(QHeaderView.Stretch)
        self.subdomain_results_table.setSelectionBehavior(QTableWidget.SelectRows)
        self.subdomain_results_table.setEditTriggers(QTableWidget.NoEditTriggers)
        layout.addWidget(self.subdomain_results_table)
        
        # Export buttons
        export_layout = QHBoxLayout()
        export_layout.addWidget(QLabel("Export:"))
        
        for fmt in ['JSON', 'CSV', 'TXT']:
            btn = QPushButton(fmt)
            btn.clicked.connect(lambda checked, f=fmt: self.export_subdomain_results(f.lower()))
            export_layout.addWidget(btn)
        
        export_layout.addStretch()
        layout.addLayout(export_layout)
        
        self.tab_widget.addTab(subdomain_tab, "Subdomains")
    
    def create_tor_tab(self):
        """Create tab for Tor/Dark Web crawling."""
        tor_tab = QWidget()
        layout = QVBoxLayout(tor_tab)
        
        # Tor configuration group
        tor_config_group = QGroupBox("Tor Configuration")
        tor_config_layout = QFormLayout()
        
        self.tor_proxy_host = QLineEdit()
        self.tor_proxy_host.setText("127.0.0.1")
        tor_config_layout.addRow("Proxy Host:", self.tor_proxy_host)
        
        self.tor_proxy_port = QSpinBox()
        self.tor_proxy_port.setRange(1, 65535)
        self.tor_proxy_port.setValue(9050)
        tor_config_layout.addRow("Proxy Port:", self.tor_proxy_port)
        
        check_tor_btn = QPushButton("Check Tor Connection")
        check_tor_btn.clicked.connect(self.check_tor_connection)
        tor_config_layout.addRow("", check_tor_btn)
        
        self.tor_status_label = QLabel("Not checked")
        tor_config_layout.addRow("Status:", self.tor_status_label)
        
        tor_config_group.setLayout(tor_config_layout)
        layout.addWidget(tor_config_group)
        
        # Tor crawl group
        tor_crawl_group = QGroupBox("Tor Crawl")
        tor_crawl_layout = QFormLayout()
        
        self.onion_url = QLineEdit()
        self.onion_url.setPlaceholderText("Enter .onion URL (e.g., http://example.onion)")
        tor_crawl_layout.addRow("Onion URL:", self.onion_url)
        
        self.onion_depth = QSpinBox()
        self.onion_depth.setRange(1, 5)
        self.onion_depth.setValue(2)
        tor_crawl_layout.addRow("Depth:", self.onion_depth)
        
        tor_crawl_btn = QPushButton("Crawl Onion Service")
        tor_crawl_btn.clicked.connect(self.perform_tor_crawl)
        tor_crawl_layout.addRow("", tor_crawl_btn)
        
        tor_crawl_group.setLayout(tor_crawl_layout)
        layout.addWidget(tor_crawl_group)
        
        # Progress bar
        self.tor_progress = QProgressBar()
        self.tor_progress.setVisible(False)
        layout.addWidget(self.tor_progress)
        
        # Results table
        self.tor_results_table = QTableWidget()
        self.tor_results_table.setColumnCount(4)
        self.tor_results_table.setHorizontalHeaderLabels(['URL', 'Type', 'Depth', 'Preview'])
        self.tor_results_table.horizontalHeader().setSectionResizeMode(QHeaderView.Stretch)
        self.tor_results_table.setSelectionBehavior(QTableWidget.SelectRows)
        self.tor_results_table.setEditTriggers(QTableWidget.NoEditTriggers)
        layout.addWidget(self.tor_results_table)
        
        self.tab_widget.addTab(tor_tab, "Tor/Dark Web")
    
    def create_whois_tab(self):
        """Create tab for WhoIs lookups."""
        whois_tab = QWidget()
        layout = QVBoxLayout(whois_tab)
        
        # WhoIs lookup group
        whois_group = QGroupBox("WhoIs Lookup")
        whois_layout = QFormLayout()
        
        self.whois_domain = QLineEdit()
        self.whois_domain.setPlaceholderText("Enter domain (e.g., example.com)")
        whois_layout.addRow("Domain:", self.whois_domain)
        
        whois_btn = QPushButton("Lookup WhoIs")
        whois_btn.clicked.connect(self.perform_whois_lookup)
        whois_layout.addRow("", whois_btn)
        
        whois_group.setLayout(whois_layout)
        layout.addWidget(whois_group)
        
        # Results display
        self.whois_results = QTextEdit()
        self.whois_results.setReadOnly(True)
        layout.addWidget(self.whois_results)
        
        self.tab_widget.addTab(whois_tab, "WhoIs")
    
    def create_port_scanner_tab(self):
        """Create tab for port scanning."""
        scanner_tab = QWidget()
        layout = QVBoxLayout(scanner_tab)
        
        # Port scanner configuration
        scanner_group = QGroupBox("Port Scanner")
        scanner_layout = QFormLayout()
        
        self.scan_host = QLineEdit()
        self.scan_host.setPlaceholderText("Enter host (e.g., example.com or 192.168.1.1)")
        scanner_layout.addRow("Host:", self.scan_host)
        
        self.scan_mode = QComboBox()
        self.scan_mode.addItems(['Common Ports', 'Custom Range', 'All Ports 1-1024'])
        scanner_layout.addRow("Scan Mode:", self.scan_mode)
        
        self.start_port = QSpinBox()
        self.start_port.setRange(1, 65535)
        self.start_port.setValue(1)
        scanner_layout.addRow("Start Port:", self.start_port)
        
        self.end_port = QSpinBox()
        self.end_port.setRange(1, 65535)
        self.end_port.setValue(1024)
        scanner_layout.addRow("End Port:", self.end_port)
        
        self.scan_timeout = QSpinBox()
        self.scan_timeout.setRange(1, 10)
        self.scan_timeout.setValue(1)
        scanner_layout.addRow("Timeout (s):", self.scan_timeout)
        
        self.async_scan = QCheckBox("Async Scan (Faster)")
        self.async_scan.setChecked(True)
        scanner_layout.addRow("", self.async_scan)
        
        scan_btn = QPushButton("Start Scan")
        scan_btn.clicked.connect(self.perform_port_scan)
        scanner_layout.addRow("", scan_btn)
        
        scanner_group.setLayout(scanner_layout)
        layout.addWidget(scanner_group)
        
        # Progress bar
        self.scan_progress = QProgressBar()
        self.scan_progress.setVisible(False)
        layout.addWidget(self.scan_progress)
        
        # Results table
        self.scan_results_table = QTableWidget()
        self.scan_results_table.setColumnCount(4)
        self.scan_results_table.setHorizontalHeaderLabels(['Port', 'Service', 'Status', 'Error'])
        self.scan_results_table.horizontalHeader().setSectionResizeMode(QHeaderView.Stretch)
        self.scan_results_table.setSelectionBehavior(QTableWidget.SelectRows)
        self.scan_results_table.setEditTriggers(QTableWidget.NoEditTriggers)
        layout.addWidget(self.scan_results_table)
        
        # Export buttons
        export_layout = QHBoxLayout()
        export_layout.addWidget(QLabel("Export:"))
        
        for fmt in ['JSON', 'CSV', 'TXT']:
            btn = QPushButton(fmt)
            btn.clicked.connect(lambda checked, f=fmt: self.export_scan_results(f.lower()))
            export_layout.addWidget(btn)
        
        export_layout.addStretch()
        layout.addLayout(export_layout)
        
        self.tab_widget.addTab(scanner_tab, "Port Scanner")
    
    def perform_search(self):
        query = self.search_query.text().strip()
        if not query:
            QMessageBox.warning(self, "Warning", "Please enter a search query")
            return
        
        engine = self.search_engine.currentText()
        num_results = self.num_results.value()
        site = self.site_filter.text().strip() or None
        file_type = self.file_type.text().strip() or None
        exact_match = self.exact_match.isChecked()
        
        self.search_progress.setVisible(True)
        self.search_progress.setRange(0, 0)
        self.search_results_table.setRowCount(0)
        
        self.search_worker = SearchWorker(self.searcher, query, engine, num_results, site, file_type, exact_match)
        self.search_worker.progress.connect(self.update_search_status)
        self.search_worker.finished.connect(self.display_search_results)
        self.search_worker.error.connect(self.handle_search_error)
        self.search_worker.start()
    
    def update_search_status(self, message):
        self.status_label.setText(message)
    
    def display_search_results(self, results):
        self.current_results = results
        self.search_progress.setVisible(False)
        self.search_progress.setRange(0, 100)
        
        self.search_results_table.setRowCount(len(results))
        
        for row, result in enumerate(results):
            if 'error' in result:
                self.search_results_table.setItem(row, 0, QTableWidgetItem(f"Error: {result['error']}"))
                self.search_results_table.setItem(row, 1, QTableWidgetItem(result.get('engine', '')))
                self.search_results_table.setItem(row, 2, QTableWidgetItem(""))
                self.search_results_table.setItem(row, 3, QTableWidgetItem(""))
            else:
                title_item = QTableWidgetItem(result.get('title', ''))
                title_item.setToolTip(result.get('title', ''))
                self.search_results_table.setItem(row, 0, title_item)
                
                url_item = QTableWidgetItem(result.get('url', ''))
                url_item.setToolTip(result.get('url', ''))
                self.search_results_table.setItem(row, 1, url_item)
                
                snippet_item = QTableWidgetItem(result.get('snippet', ''))
                snippet_item.setToolTip(result.get('snippet', ''))
                self.search_results_table.setItem(row, 2, snippet_item)
                
                self.search_results_table.setItem(row, 3, QTableWidgetItem(result.get('engine', '')))
        
        self.status_label.setText(f"Search complete. Found {len(results)} results")
    
    def handle_search_error(self, error_msg):
        self.search_progress.setVisible(False)
        self.search_progress.setRange(0, 100)
        QMessageBox.critical(self, "Search Error", error_msg)
        self.status_label.setText("Search failed")
    
    def perform_crawl(self):
        url = self.crawl_url.text().strip()
        if not url:
            QMessageBox.warning(self, "Warning", "Please enter a URL to crawl")
            return
        
        depth = self.crawl_depth.value()
        search_text = [t.strip() for t in self.search_text.text().split(',') if t.strip()] or None
        search_names = [n.strip() for n in self.search_names.text().split(',') if n.strip()] or None
        file_extensions = [e.strip() for e in self.file_extensions.text().split(',') if e.strip()] or None
        use_regex = self.use_regex.isChecked()
        
        # Advanced features
        use_async = self.use_async.isChecked()
        use_js_rendering = self.use_js_rendering.isChecked()
        respect_robots = self.respect_robots.isChecked()
        polite_crawling = self.polite_crawling.isChecked()
        max_concurrent = self.max_concurrent.value()
        rate_limit_delay = self.rate_limit_delay.value()
        
        # Authentication
        auth_type = self.auth_type.currentText()
        auth_credentials = None
        
        if auth_type == 'Basic Auth':
            username = self.auth_username.text().strip()
            password = self.auth_password.text().strip()
            if username and password:
                auth_credentials = {'type': 'basic', 'username': username, 'password': password}
        elif auth_type == 'Bearer Token':
            token = self.auth_token.text().strip()
            if token:
                auth_credentials = {'type': 'bearer', 'token': token}
        elif auth_type == 'Session-based':
            login_url = self.login_url.text().strip()
            if login_url:
                auth_credentials = {'type': 'session', 'login_url': login_url, 'login_data': {}}
        
        self.crawler = Crawler(url, depth)
        
        self.crawl_progress.setVisible(True)
        self.crawl_progress.setRange(0, 0)
        self.crawl_results_table.setRowCount(0)
        
        self.crawl_worker = CrawlWorker(
            self.crawler, search_text, search_names, file_extensions, use_regex,
            use_async, use_js_rendering, respect_robots, polite_crawling,
            max_concurrent, rate_limit_delay, auth_credentials
        )
        self.crawl_worker.progress.connect(self.update_crawl_status)
        self.crawl_worker.finished.connect(self.display_crawl_results)
        self.crawl_worker.error.connect(self.handle_crawl_error)
        self.crawl_worker.start()
    
    def update_crawl_status(self, message):
        self.status_label.setText(message)
    
    def display_crawl_results(self, results):
        self.current_results = results
        self.crawl_progress.setVisible(False)
        self.crawl_progress.setRange(0, 100)
        
        self.crawl_results_table.setRowCount(len(results))
        
        for row, result in enumerate(results):
            url_item = QTableWidgetItem(result.get('url', ''))
            url_item.setToolTip(result.get('url', ''))
            self.crawl_results_table.setItem(row, 0, url_item)
            
            self.crawl_results_table.setItem(row, 1, QTableWidgetItem(result.get('type', '')))
            self.crawl_results_table.setItem(row, 2, QTableWidgetItem(str(result.get('depth', 0))))
            
            match_info = []
            if result.get('matched_text'):
                match_info.append(f"Text: {result['matched_text']}")
            if result.get('matched_name'):
                match_info.append(f"Name: {result['matched_name']}")
            if result.get('matched_extension'):
                match_info.append(f"Ext: {result['matched_extension']}")
            
            match_item = QTableWidgetItem(', '.join(match_info))
            self.crawl_results_table.setItem(row, 3, match_item)
            
            preview = result.get('content_preview', '') or result.get('error', '') or result.get('content_type', '')
            preview_item = QTableWidgetItem(preview[:100] if preview else '')
            preview_item.setToolTip(preview)
            self.crawl_results_table.setItem(row, 4, preview_item)
            
            # Color code rows
            if result.get('type') == 'error':
                for col in range(5):
                    self.crawl_results_table.item(row, col).setBackground(QColor(255, 200, 200))
            elif result.get('type') == 'file':
                for col in range(5):
                    self.crawl_results_table.item(row, col).setBackground(QColor(200, 255, 200))
        
        self.status_label.setText(f"Crawl complete. Found {len(results)} results")
    
    def handle_crawl_error(self, error_msg):
        self.crawl_progress.setVisible(False)
        self.crawl_progress.setRange(0, 100)
        QMessageBox.critical(self, "Crawl Error", error_msg)
        self.status_label.setText("Crawl failed")
    
    def export_search_results(self, format):
        if not self.current_results:
            QMessageBox.warning(self, "Warning", "No results to export")
            return
        
        filename, _ = QFileDialog.getSaveFileName(
            self, f"Export Search Results as {format.upper()}", 
            f"search_results.{format}", 
            f"{format.upper()} files (*.{format})"
        )
        
        if filename:
            if self.exporter.export(self.current_results, filename, format, "Search Results"):
                QMessageBox.information(self, "Success", f"Results exported to {filename}")
            else:
                QMessageBox.critical(self, "Error", "Failed to export results")
    
    def export_crawl_results(self, format):
        if not self.current_results:
            QMessageBox.warning(self, "Warning", "No results to export")
            return
        
        filename, _ = QFileDialog.getSaveFileName(
            self, f"Export Crawl Results as {format.upper()}", 
            f"crawl_results.{format}", 
            f"{format.upper()} files (*.{format})"
        )
        
        if filename:
            if self.exporter.export(self.current_results, filename, format, "Crawl Results"):
                QMessageBox.information(self, "Success", f"Results exported to {filename}")
            else:
                QMessageBox.critical(self, "Error", "Failed to export results")
    
    # Advanced Search handlers
    def parse_operators(self):
        query = self.advanced_query.text().strip()
        if not query:
            QMessageBox.warning(self, "Warning", "Please enter a query")
            return
        
        operators = self.operator_parser.parse(query)
        
        result_text = f"Query: {operators.query}\n"
        if operators.site:
            result_text += f"Site: {operators.site}\n"
        if operators.intitle:
            result_text += f"Intitle: {operators.intitle}\n"
        if operators.inurl:
            result_text += f"InURL: {operators.inurl}\n"
        if operators.filetype:
            result_text += f"Filetype: {operators.filetype}\n"
        
        self.parsed_operators.setText(result_text)
    
    def expand_query(self):
        query = self.expand_query_input.text().strip()
        if not query:
            QMessageBox.warning(self, "Warning", "Please enter a query")
            return
        
        expanded = self.query_expander.expand_query(
            query, 
            use_synonyms=self.use_synonyms.isChecked(),
            use_variations=self.use_variations.isChecked()
        )
        
        self.expanded_queries.setText('\n'.join(expanded))
    
    # Multi-Engine handlers
    def perform_multi_engine_search(self):
        query = self.multi_query.text().strip()
        if not query:
            QMessageBox.warning(self, "Warning", "Please enter a search query")
            return
        
        num_results = self.multi_num_results.value()
        expand = self.expand_multi_query.isChecked()
        
        self.multi_progress.setVisible(True)
        self.multi_progress.setRange(0, 0)
        self.multi_results_table.setRowCount(0)
        
        # Run in thread to avoid blocking GUI
        self.multi_engine_thread = MultiEngineWorker(
            self.multi_engine_aggregator, query, num_results, expand
        )
        self.multi_engine_thread.progress.connect(self.update_multi_status)
        self.multi_engine_thread.finished.connect(self.display_multi_results)
        self.multi_engine_thread.error.connect(self.handle_multi_error)
        self.multi_engine_thread.start()
    
    def update_multi_status(self, message):
        self.status_label.setText(message)
    
    def display_multi_results(self, results):
        self.current_results = results
        self.multi_progress.setVisible(False)
        self.multi_progress.setRange(0, 100)
        
        self.multi_results_table.setRowCount(len(results))
        
        for row, result in enumerate(results):
            self.multi_results_table.setItem(row, 0, QTableWidgetItem(result.get('title', '')))
            self.multi_results_table.setItem(row, 1, QTableWidgetItem(result.get('url', '')))
            self.multi_results_table.setItem(row, 2, QTableWidgetItem(result.get('snippet', '')))
            self.multi_results_table.setItem(row, 3, QTableWidgetItem(result.get('search_engine', '')))
            self.multi_results_table.setItem(row, 4, QTableWidgetItem(str(result.get('relevance_score', 0))))
        
        self.status_label.setText(f"Multi-engine search complete. Found {len(results)} results")
    
    def handle_multi_error(self, error_msg):
        self.multi_progress.setVisible(False)
        self.multi_progress.setRange(0, 100)
        QMessageBox.critical(self, "Multi-Engine Error", error_msg)
        self.status_label.setText("Multi-engine search failed")
    
    def export_multi_results(self, format):
        if not self.current_results:
            QMessageBox.warning(self, "Warning", "No results to export")
            return
        
        filename, _ = QFileDialog.getSaveFileName(
            self, f"Export Multi-Engine Results as {format.upper()}", 
            f"multi_engine_results.{format}", 
            f"{format.upper()} files (*.{format})"
        )
        
        if filename:
            if self.exporter.export(self.current_results, filename, format, "Multi-Engine Results"):
                QMessageBox.information(self, "Success", f"Results exported to {filename}")
            else:
                QMessageBox.critical(self, "Error", "Failed to export results")
    
    # Subdomain Discovery handlers
    def perform_subdomain_discovery(self):
        domain = self.subdomain_domain.text().strip()
        if not domain:
            QMessageBox.warning(self, "Warning", "Please enter a domain")
            return
        
        use_dns = self.use_dns_brute.isChecked()
        use_crtsh = self.use_crtsh.isChecked()
        
        self.subdomain_progress.setVisible(True)
        self.subdomain_progress.setRange(0, 0)
        self.subdomain_results_table.setRowCount(0)
        
        # Run in thread
        self.subdomain_thread = SubdomainWorker(
            self.subdomain_discovery, domain, use_dns, use_crtsh
        )
        self.subdomain_thread.progress.connect(self.update_subdomain_status)
        self.subdomain_thread.finished.connect(self.display_subdomain_results)
        self.subdomain_thread.error.connect(self.handle_subdomain_error)
        self.subdomain_thread.start()
    
    def update_subdomain_status(self, message):
        self.status_label.setText(message)
    
    def display_subdomain_results(self, results):
        self.current_results = results
        self.subdomain_progress.setVisible(False)
        self.subdomain_progress.setRange(0, 100)
        
        # Flatten results for display
        all_results = []
        for method, subdomains in results.items():
            if method != 'all':
                for subdomain in subdomains:
                    all_results.append({'subdomain': subdomain, 'method': method, 'status': 'found'})
        
        self.subdomain_results_table.setRowCount(len(all_results))
        
        for row, result in enumerate(all_results):
            self.subdomain_results_table.setItem(row, 0, QTableWidgetItem(result['subdomain']))
            self.subdomain_results_table.setItem(row, 1, QTableWidgetItem(result['method']))
            self.subdomain_results_table.setItem(row, 2, QTableWidgetItem(result['status']))
        
        total = len(results.get('all', set()))
        self.status_label.setText(f"Subdomain discovery complete. Found {total} unique subdomains")
    
    def handle_subdomain_error(self, error_msg):
        self.subdomain_progress.setVisible(False)
        self.subdomain_progress.setRange(0, 100)
        QMessageBox.critical(self, "Subdomain Error", error_msg)
        self.status_label.setText("Subdomain discovery failed")
    
    def export_subdomain_results(self, format):
        if not self.current_results:
            QMessageBox.warning(self, "Warning", "No results to export")
            return
        
        # Convert to list format for export
        export_data = []
        for method, subdomains in self.current_results.items():
            if method != 'all':
                for subdomain in subdomains:
                    export_data.append({'subdomain': subdomain, 'method': method})
        
        filename, _ = QFileDialog.getSaveFileName(
            self, f"Export Subdomain Results as {format.upper()}", 
            f"subdomain_results.{format}", 
            f"{format.upper()} files (*.{format})"
        )
        
        if filename:
            if self.exporter.export(export_data, filename, format, "Subdomain Results"):
                QMessageBox.information(self, "Success", f"Results exported to {filename}")
            else:
                QMessageBox.critical(self, "Error", "Failed to export results")
    
    # Tor handlers
    def check_tor_connection(self):
        host = self.tor_proxy_host.text().strip()
        port = self.tor_proxy_port.value()
        
        self.tor_crawler.proxy_host = host
        self.tor_crawler.proxy_port = port
        
        if self.tor_crawler.check_tor_connection():
            self.tor_status_label.setText("Connected ✓")
            self.tor_status_label.setStyleSheet("color: green")
            QMessageBox.information(self, "Tor Status", "Successfully connected to Tor!")
        else:
            self.tor_status_label.setText("Failed ✗")
            self.tor_status_label.setStyleSheet("color: red")
            QMessageBox.warning(self, "Tor Status", "Failed to connect to Tor. Make sure Tor is running.")
    
    def perform_tor_crawl(self):
        url = self.onion_url.text().strip()
        if not url:
            QMessageBox.warning(self, "Warning", "Please enter an .onion URL")
            return
        
        depth = self.onion_depth.value()
        
        self.tor_progress.setVisible(True)
        self.tor_progress.setRange(0, 0)
        self.tor_results_table.setRowCount(0)
        
        # Run in thread
        self.tor_thread = TorWorker(self.tor_crawler, url, depth)
        self.tor_thread.progress.connect(self.update_tor_status)
        self.tor_thread.finished.connect(self.display_tor_results)
        self.tor_thread.error.connect(self.handle_tor_error)
        self.tor_thread.start()
    
    def update_tor_status(self, message):
        self.status_label.setText(message)
    
    def display_tor_results(self, results):
        self.current_results = results
        self.tor_progress.setVisible(False)
        self.tor_progress.setRange(0, 100)
        
        self.tor_results_table.setRowCount(len(results))
        
        for row, result in enumerate(results):
            self.tor_results_table.setItem(row, 0, QTableWidgetItem(result.get('url', '')))
            self.tor_results_table.setItem(row, 1, QTableWidgetItem(result.get('type', '')))
            self.tor_results_table.setItem(row, 2, QTableWidgetItem(str(result.get('depth', 0))))
            preview = result.get('content_preview', '') or result.get('error', '')[:100]
            self.tor_results_table.setItem(row, 3, QTableWidgetItem(preview))
        
        self.status_label.setText(f"Tor crawl complete. Found {len(results)} results")
    
    def handle_tor_error(self, error_msg):
        self.tor_progress.setVisible(False)
        self.tor_progress.setRange(0, 100)
        QMessageBox.critical(self, "Tor Error", error_msg)
        self.status_label.setText("Tor crawl failed")
    
    # WhoIs handlers
    def perform_whois_lookup(self):
        domain = self.whois_domain.text().strip()
        if not domain:
            QMessageBox.warning(self, "Warning", "Please enter a domain")
            return
        
        result = self.whois_search.lookup(domain)
        
        if 'error' in result:
            self.whois_results.setText(f"Error: {result['error']}")
        else:
            output = f"Domain: {result.get('domain_name', 'N/A')}\n"
            output += f"Registrar: {result.get('registrar', 'N/A')}\n"
            output += f"Creation Date: {result.get('creation_date', 'N/A')}\n"
            output += f"Expiration Date: {result.get('expiration_date', 'N/A')}\n"
            output += f"Updated Date: {result.get('updated_date', 'N/A')}\n"
            output += f"Name Servers: {', '.join(map(str, result.get('name_servers', [])))}\n"
            output += f"Status: {', '.join(map(str, result.get('status', [])))}\n"
            output += f"Emails: {', '.join(map(str, result.get('emails', [])))}\n"
            output += f"Organization: {result.get('org', 'N/A')}\n"
            output += f"Country: {result.get('country', 'N/A')}\n"
            
            self.whois_results.setText(output)
        
        self.status_label.setText(f"WhoIs lookup complete for {domain}")
    
    # Port Scanner handlers
    def perform_port_scan(self):
        host = self.scan_host.text().strip()
        if not host:
            QMessageBox.warning(self, "Warning", "Please enter a host")
            return
        
        mode = self.scan_mode.currentText()
        timeout = self.scan_timeout.value()
        use_async = self.async_scan.isChecked()
        
        if mode == 'Common Ports':
            ports = None
        elif mode == 'Custom Range':
            ports = list(range(self.start_port.value(), self.end_port.value() + 1))
        else:  # All Ports 1-1024
            ports = list(range(1, 1025))
        
        self.port_scanner.timeout = timeout
        
        self.scan_progress.setVisible(True)
        self.scan_progress.setRange(0, 0)
        self.scan_results_table.setRowCount(0)
        
        # Run in thread
        self.scan_thread = PortScanWorker(self.port_scanner, host, ports, use_async)
        self.scan_thread.progress.connect(self.update_scan_status)
        self.scan_thread.finished.connect(self.display_scan_results)
        self.scan_thread.error.connect(self.handle_scan_error)
        self.scan_thread.start()
    
    def update_scan_status(self, message):
        self.status_label.setText(message)
    
    def display_scan_results(self, results):
        self.current_results = results
        self.scan_progress.setVisible(False)
        self.scan_progress.setRange(0, 100)
        
        self.scan_results_table.setRowCount(len(results))
        
        for row, result in enumerate(results):
            self.scan_results_table.setItem(row, 0, QTableWidgetItem(str(result['port'])))
            self.scan_results_table.setItem(row, 1, QTableWidgetItem(result['service']))
            
            status_item = QTableWidgetItem(result['status'])
            if result['status'] == 'open':
                status_item.setBackground(QColor(200, 255, 200))
            self.scan_results_table.setItem(row, 2, status_item)
            
            self.scan_results_table.setItem(row, 3, QTableWidgetItem(result.get('error', '')))
        
        open_ports = len([r for r in results if r['status'] == 'open'])
        self.status_label.setText(f"Port scan complete. {open_ports} open ports found")
    
    def handle_scan_error(self, error_msg):
        self.scan_progress.setVisible(False)
        self.scan_progress.setRange(0, 100)
        QMessageBox.critical(self, "Scan Error", error_msg)
        self.status_label.setText("Port scan failed")
    
    def export_scan_results(self, format):
        if not self.current_results:
            QMessageBox.warning(self, "Warning", "No results to export")
            return
        
        filename, _ = QFileDialog.getSaveFileName(
            self, f"Export Scan Results as {format.upper()}", 
            f"scan_results.{format}", 
            f"{format.upper()} files (*.{format})"
        )
        
        if filename:
            if self.exporter.export(self.current_results, filename, format, "Port Scan Results"):
                QMessageBox.information(self, "Success", f"Results exported to {filename}")
            else:
                QMessageBox.critical(self, "Error", "Failed to export results")

# Worker classes for new features
class MultiEngineWorker(QThread):
    progress = pyqtSignal(str)
    finished = pyqtSignal(list)
    error = pyqtSignal(str)
    
    def __init__(self, aggregator, query, num_results, expand_query):
        super().__init__()
        self.aggregator = aggregator
        self.query = query
        self.num_results = num_results
        self.expand_query = expand_query
    
    def run(self):
        try:
            self.progress.emit(f"Searching across multiple engines for: {self.query}")
            results = self.aggregator.search_all(self.query, self.num_results, self.expand_query)
            self.progress.emit(f"Found {len(results)} aggregated results")
            self.finished.emit(results)
        except Exception as e:
            self.error.emit(str(e))

class SubdomainWorker(QThread):
    progress = pyqtSignal(str)
    finished = pyqtSignal(dict)
    error = pyqtSignal(str)
    
    def __init__(self, discovery, domain, use_dns, use_crtsh):
        super().__init__()
        self.discovery = discovery
        self.domain = domain
        self.use_dns = use_dns
        self.use_crtsh = use_crtsh
    
    def run(self):
        try:
            self.progress.emit(f"Discovering subdomains for: {self.domain}")
            
            def progress_callback(current, total, found):
                self.progress.emit(f"Progress: {current}/{total}, Found: {found}")
            
            results = self.discovery.discover_subdomains(
                self.domain, 
                use_dns_brute=self.use_dns,
                use_crtsh=self.use_crtsh,
                progress_callback=progress_callback
            )
            
            total = len(results.get('all', set()))
            self.progress.emit(f"Discovery complete. Found {total} unique subdomains")
            self.finished.emit(results)
        except Exception as e:
            self.error.emit(str(e))

class TorWorker(QThread):
    progress = pyqtSignal(str)
    finished = pyqtSignal(list)
    error = pyqtSignal(str)
    
    def __init__(self, tor_crawler, url, depth):
        super().__init__()
        self.tor_crawler = tor_crawler
        self.url = url
        self.depth = depth
    
    def run(self):
        try:
            self.progress.emit(f"Crawling .onion service: {self.url}")
            results = self.tor_crawler.crawl_onion(self.url, self.depth)
            self.progress.emit(f"Tor crawl complete. Found {len(results)} results")
            self.finished.emit(results)
        except Exception as e:
            self.error.emit(str(e))

class PortScanWorker(QThread):
    progress = pyqtSignal(str)
    finished = pyqtSignal(list)
    error = pyqtSignal(str)
    
    def __init__(self, scanner, host, ports, use_async):
        super().__init__()
        self.scanner = scanner
        self.host = host
        self.ports = ports
        self.use_async = use_async
    
    def run(self):
        try:
            self.progress.emit(f"Scanning ports on: {self.host}")
            
            def progress_callback(current, total, open_count):
                self.progress.emit(f"Progress: {current}/{total}, Open ports: {open_count}")
            
            if self.use_async:
                results = self.scanner.async_scan_ports(self.host, self.ports)
            else:
                results = self.scanner.scan_ports(self.host, self.ports, progress_callback)
            
            open_ports = len([r for r in results if r['status'] == 'open'])
            self.progress.emit(f"Scan complete. {open_ports} open ports found")
            self.finished.emit(results)
        except Exception as e:
            self.error.emit(str(e))

if __name__ == "__main__":
    app = QApplication([])
    window = GUI()
    window.show()
    app.exec_()