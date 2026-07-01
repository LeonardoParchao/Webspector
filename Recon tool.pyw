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
try:
    from simhash import Simhash
except ImportError:
    Simhash = None
try:
    from playwright.async_api import async_playwright
except ImportError:
    async_playwright = None
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
        self.init_ui()
    
    def init_ui(self):
        self.setWindowTitle("Recon Tool - Web Search & Crawler")
        self.setGeometry(100, 100, 1200, 800)
        
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

if __name__ == "__main__":
    app = QApplication([])
    window = GUI()
    window.show()
    app.exec_()