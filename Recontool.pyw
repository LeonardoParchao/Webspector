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

# Advanced feature imports
try:
    import networkx as nx
    import matplotlib.pyplot as plt
    from matplotlib.backends.backend_qt5agg import FigureCanvasQTAgg as FigureCanvas
except ImportError:
    nx = None
    plt = None

try:
    from transformers import pipeline, AutoTokenizer, AutoModelForSequenceClassification
except ImportError:
    pipeline = None
    AutoTokenizer = None
    AutoModelForSequenceClassification = None

try:
    import spacy
except ImportError:
    spacy = None

try:
    from PIL import Image
    import imagehash
except ImportError:
    Image = None
    imagehash = None

try:
    import pytesseract
except ImportError:
    pytesseract = None

try:
    import plotly.graph_objects as go
    from plotly.subplots import make_subplots
except ImportError:
    go = None
    make_subplots = None

try:
    from PyQtWebEngine.QtWebEngineWidgets import QWebEngineView
    from PyQtWebEngine.QtCore import QUrl
except ImportError:
    QWebEngineView = None
    QUrl = None

try:
    import numpy as np
except ImportError:
    np = None

# New feature imports
try:
    import ssl
    from ssl import SSLContext
except ImportError:
    ssl = None

try:
    import OpenSSL
    from OpenSSL import crypto
except ImportError:
    OpenSSL = None

try:
    import geoip2.database
    import geoip2.records
except ImportError:
    geoip2 = None

try:
    import folium
except ImportError:
    folium = None

try:
    import aiohttp
except ImportError:
    aiohttp = None

try:
    import praw
except ImportError:
    praw = None

try:
    import mastodon
except ImportError:
    mastodon = None

try:
    import ipaddress
except ImportError:
    ipaddress = None

try:
    from cryptography.fernet import Fernet
    from cryptography.hazmat.primitives import hashes
    from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC
    import base64
    import os
except ImportError:
    Fernet = None
    hashes = None
    PBKDF2HMAC = None
    base64 = None
    os = None

from PyQt5.QtWidgets import (QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout, 
                             QTabWidget, QLabel, QLineEdit, QPushButton, QComboBox, 
                             QSpinBox, QDoubleSpinBox, QCheckBox, QTextEdit, QTableWidget, QTableWidgetItem,
                             QHeaderView, QFileDialog, QMessageBox, QGroupBox, QSplitter,
                             QProgressBar, QFormLayout, QScrollArea)
from PyQt5.QtCore import Qt, QThread, pyqtSignal, QMutex, QMutexLocker
from PyQt5.QtGui import QFont, QColor
import traceback
import sys

# Security and validation utilities
class APIKeyManager:
    """Secure API key storage and encryption."""
    
    def __init__(self):
        self._fernet = None
        self._init_encryption()
    
    def _init_encryption(self):
        """Initialize encryption with a key derived from machine-specific data."""
        if Fernet is None:
            print("Warning: cryptography library not available. API keys will be stored in plain text.")
            return
        
        try:
            # Derive a key from machine-specific data (in production, use proper key management)
            machine_id = os.environ.get('COMPUTERNAME', 'default') + os.environ.get('USERNAME', 'default')
            kdf = PBKDF2HMAC(
                algorithm=hashes.SHA256(),
                length=32,
                salt=b'recon_tool_salt',  # In production, use random salt stored securely
                iterations=100000,
            )
            key = base64.urlsafe_b64encode(kdf.derive(machine_id.encode()))
            self._fernet = Fernet(key)
        except Exception as e:
            print(f"Warning: Failed to initialize encryption: {e}")
    
    def encrypt_key(self, api_key: str) -> str:
        """Encrypt an API key."""
        if self._fernet is None:
            return api_key  # Fallback to plain text
        try:
            return self._fernet.encrypt(api_key.encode()).decode()
        except Exception as e:
            print(f"Encryption failed: {e}")
            return api_key
    
    def decrypt_key(self, encrypted_key: str) -> str:
        """Decrypt an API key."""
        if self._fernet is None:
            return encrypted_key  # Return as-is if encryption not available
        try:
            return self._fernet.decrypt(encrypted_key.encode()).decode()
        except Exception as e:
            print(f"Decryption failed: {e}")
            return encrypted_key

class InputValidator:
    """Strict input validation for URLs, IPs, ports, and other user inputs."""
    
    @staticmethod
    def validate_url(url: str) -> tuple[bool, str]:
        """Validate URL format and scheme."""
        if not url or not url.strip():
            return False, "URL cannot be empty"
        
        url = url.strip()
        
        try:
            parsed = urlparse(url)
            
            # Check scheme
            if parsed.scheme not in ['http', 'https']:
                return False, "URL must use http or https scheme"
            
            # Check netloc (domain/IP)
            if not parsed.netloc:
                return False, "URL must contain a valid domain or IP address"
            
            # Check for suspicious patterns (potential injection)
            dangerous_patterns = ['<script', 'javascript:', 'data:', 'vbscript:', 'onload=', 'onerror=']
            for pattern in dangerous_patterns:
                if pattern.lower() in url.lower():
                    return False, f"URL contains potentially dangerous pattern: {pattern}"
            
            return True, "Valid URL"
        except Exception as e:
            return False, f"Invalid URL format: {str(e)}"
    
    @staticmethod
    def validate_ip(ip: str) -> tuple[bool, str]:
        """Validate IP address format."""
        if not ip or not ip.strip():
            return False, "IP address cannot be empty"
        
        ip = ip.strip()
        
        try:
            if ipaddress is None:
                return True, "IP validation not available (ipaddress module missing)"
            
            ipaddress.ip_address(ip)
            
            # Check for localhost/private ranges if needed
            # ip_obj = ipaddress.ip_address(ip)
            # if ip_obj.is_private:
            #     return True, "Valid private IP"
            
            return True, "Valid IP address"
        except ValueError:
            return False, "Invalid IP address format"
        except Exception as e:
            return False, f"IP validation error: {str(e)}"
    
    @staticmethod
    def validate_port(port: int) -> tuple[bool, str]:
        """Validate port number."""
        if not isinstance(port, int):
            return False, "Port must be a number"
        
        if port < 1 or port > 65535:
            return False, "Port must be between 1 and 65535"
        
        return True, "Valid port"
    
    @staticmethod
    def validate_port_range(start_port: int, end_port: int) -> tuple[bool, str]:
        """Validate port range."""
        valid_start, msg_start = InputValidator.validate_port(start_port)
        if not valid_start:
            return False, f"Invalid start port: {msg_start}"
        
        valid_end, msg_end = InputValidator.validate_port(end_port)
        if not valid_end:
            return False, f"Invalid end port: {msg_end}"
        
        if start_port > end_port:
            return False, "Start port cannot be greater than end port"
        
        # Prevent excessive ranges
        if (end_port - start_port) > 10000:
            return False, "Port range too large (maximum 10000 ports)"
        
        return True, "Valid port range"
    
    @staticmethod
    def validate_domain(domain: str) -> tuple[bool, str]:
        """Validate domain name format."""
        if not domain or not domain.strip():
            return False, "Domain cannot be empty"
        
        domain = domain.strip().lower()
        
        # Basic domain validation
        if len(domain) > 253:
            return False, "Domain too long (maximum 253 characters)"
        
        # Check for valid characters
        if not re.match(r'^[a-z0-9]([a-z0-9-]{0,61}[a-z0-9])?(\.[a-z0-9]([a-z0-9-]{0,61}[a-z0-9])?)*$', domain):
            return False, "Invalid domain format"
        
        # Check for dangerous patterns
        dangerous_patterns = ['<script', 'javascript:', 'onload=', 'onerror=']
        for pattern in dangerous_patterns:
            if pattern.lower() in domain.lower():
                return False, f"Domain contains potentially dangerous pattern: {pattern}"
        
        return True, "Valid domain"
    
    @staticmethod
    def sanitize_input(input_str: str, max_length: int = 1000) -> str:
        """Sanitize user input to prevent injection attacks."""
        if not input_str:
            return ""
        
        # Truncate to max length
        input_str = input_str[:max_length]
        
        # Remove potentially dangerous characters
        dangerous_chars = ['<', '>', '"', "'", '&', '\x00', '\n', '\r']
        for char in dangerous_chars:
            input_str = input_str.replace(char, '')
        
        return input_str.strip()

class ThreadPoolManager:
    """Manage thread pool to prevent resource exhaustion."""
    
    _instance = None
    _mutex = QMutex()
    
    def __new__(cls):
        with QMutexLocker(cls._mutex):
            if cls._instance is None:
                cls._instance = super().__new__(cls)
                cls._instance._active_threads = []
                cls._instance._max_threads = 10  # Maximum concurrent threads
        return cls._instance
    
    def can_start_thread(self) -> bool:
        """Check if a new thread can be started."""
        with QMutexLocker(self._mutex):
            # Count active threads
            active_count = sum(1 for t in self._active_threads if t.isRunning())
            return active_count < self._max_threads
    
    def register_thread(self, thread: QThread):
        """Register a new thread."""
        with QMutexLocker(self._mutex):
            self._active_threads.append(thread)
    
    def unregister_thread(self, thread: QThread):
        """Unregister a thread."""
        with QMutexLocker(self._mutex):
            if thread in self._active_threads:
                self._active_threads.remove(thread)
    
    def get_active_count(self) -> int:
        """Get count of active threads."""
        with QMutexLocker(self._mutex):
            return sum(1 for t in self._active_threads if t.isRunning())
    
    def set_max_threads(self, max_threads: int):
        """Set maximum number of concurrent threads."""
        with QMutexLocker(self._mutex):
            self._max_threads = max(1, min(50, max_threads))  # Limit between 1 and 50

class CancellableOperation:
    """Base class for cancellable operations."""
    
    def __init__(self):
        self._cancelled = False
        self._mutex = QMutex()
    
    def is_cancelled(self) -> bool:
        """Check if operation is cancelled."""
        with QMutexLocker(self._mutex):
            return self._cancelled
    
    def cancel(self):
        """Cancel the operation."""
        with QMutexLocker(self._mutex):
            self._cancelled = True

class Crawler(CancellableOperation):
    def __init__(self, url: str, depth: int, 
                 use_async: bool = True,
                 use_js_rendering: bool = False,
                 respect_robots: bool = True,
                 polite_crawling: bool = True,
                 max_concurrent: int = 10,
                 rate_limit_delay: float = 1.0,
                 auth_credentials: Optional[Dict] = None,
                 use_disk_cache: bool = False,
                 max_memory_results: int = 1000):
        super().__init__()
        
        # Validate URL
        is_valid, msg = InputValidator.validate_url(url)
        if not is_valid:
            raise ValueError(f"Invalid URL: {msg}")
        
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
        
        # Memory optimization
        self.use_disk_cache = use_disk_cache
        self.max_memory_results = max_memory_results
        self._cache_dir = "crawl_cache"
        self._disk_cache_file = None
        
        if self.use_disk_cache:
            import os
            os.makedirs(self._cache_dir, exist_ok=True)
        
        # Rate limiting and backoff
        self.domain_last_request: Dict[str, float] = {}
        self.domain_retry_count: Dict[str, int] = {}
        self.max_retries = 3
        
        # Robots.txt cache
        self.robots_cache: Dict[str, RobotFileParser] = {}
        
        # Content fingerprinting
        self.content_hashes: Dict[str, Simhash] = {}
        self.near_duplicate_threshold = 0.85
        
        # Authentication
        if auth_credentials:
            self._setup_authentication()
        
        # Playwright browser (lazy initialization)
        self.playwright_browser = None
        self.playwright_context = None
        self.playwright_instance = None
    
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
    
    def _add_result(self, result: Dict):
        """Add result with memory management."""
        if self.use_disk_cache and len(self.results) >= self.max_memory_results:
            # Flush to disk cache
            self._flush_to_disk()
        
        self.results.append(result)
    
    def _flush_to_disk(self):
        """Flush results to disk cache for memory optimization."""
        if not self.results:
            return
        
        try:
            import os
            import json
            from datetime import datetime
            
            if self._disk_cache_file is None:
                timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
                self._disk_cache_file = os.path.join(self._cache_dir, f"crawl_{timestamp}.json")
            
            with open(self._disk_cache_file, 'a', encoding='utf-8') as f:
                for result in self.results:
                    f.write(json.dumps(result) + '\n')
            
            self.results.clear()
        except Exception as e:
            print(f"Error flushing to disk cache: {e}")
    
    def _load_from_disk(self) -> List[Dict]:
        """Load results from disk cache."""
        all_results = []
        
        try:
            import os
            if os.path.exists(self._cache_dir):
                for filename in os.listdir(self._cache_dir):
                    if filename.startswith('crawl_') and filename.endswith('.json'):
                        filepath = os.path.join(self._cache_dir, filename)
                        with open(filepath, 'r', encoding='utf-8') as f:
                            for line in f:
                                try:
                                    all_results.append(json.loads(line.strip()))
                                except json.JSONDecodeError:
                                    continue
        except Exception as e:
            print(f"Error loading from disk cache: {e}")
        
        return all_results + self.results
    
    def get_results(self) -> List[Dict]:
        """Return the crawl results, loading from disk if needed."""
        if self.use_disk_cache:
            return self._load_from_disk()
        return self.results
    
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
    
    def _compute_simhash(self, content: str) -> Optional[Simhash]:
        """Compute Simhash for content using word shingling."""
        if Simhash is None:
            return None
        
        # Tokenize content into words and create shingles (3-word sequences)
        words = re.findall(r'\w+', content.lower())
        shingles = [' '.join(words[i:i+3]) for i in range(len(words) - 2)]
        
        # Compute Simhash from shingles
        return Simhash(shingles)
    
    def _is_near_duplicate(self, content: str) -> bool:
        """Check if content is near-duplicate using simhash."""
        if Simhash is None:
            return False
        
        content_simhash = self._compute_simhash(content)
        if content_simhash is None:
            return False
        
        for existing_simhash in self.content_hashes.values():
            # Compute Hamming distance between Simhash values
            distance = content_simhash.distance(existing_simhash)
            # Convert distance to similarity (lower distance = higher similarity)
            # Simhash uses 64-bit hashes, so max distance is 64
            similarity = 1 - (distance / 64)
            
            if similarity >= self.near_duplicate_threshold:
                return True
        
        return False
    
    async def _render_with_playwright(self, url: str) -> Optional[str]:
        """Render page with Playwright for JavaScript content."""
        if async_playwright is None:
            return None
        
        try:
            if self.playwright_browser is None:
                self.playwright_instance = await async_playwright().start()
                self.playwright_browser = await self.playwright_instance.chromium.launch(headless=True)
                self.playwright_context = await self.playwright_browser.new_context()
            
            page = await self.playwright_context.new_page()
            await page.goto(url, wait_until='networkidle', timeout=30000)
            content = await page.content()
            await page.close()
            return content
        except Exception as e:
            print(f"Playwright rendering failed: {e}")
            # Ensure cleanup on error
            await self._close_playwright()
            return None
    
    async def _close_playwright(self):
        """Close Playwright browser with proper cleanup."""
        try:
            if self.playwright_context:
                await self.playwright_context.close()
                self.playwright_context = None
        except Exception as e:
            print(f"Error closing Playwright context: {e}")
        
        try:
            if self.playwright_browser:
                await self.playwright_browser.close()
                self.playwright_browser = None
        except Exception as e:
            print(f"Error closing Playwright browser: {e}")
        
        try:
            if self.playwright_instance:
                await self.playwright_instance.stop()
                self.playwright_instance = None
        except Exception as e:
            print(f"Error stopping Playwright instance: {e}")
        
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
    
    async def _fetch_page_async(self, session: aiohttp.ClientSession, url: str) -> Optional[Dict]:
        """Fetch a single page asynchronously."""
        await self._async_apply_rate_limit(url)
        
        if not self._can_fetch(url):
            return None
        
        try:
            start_time = time.time()
            async with session.get(url, timeout=aiohttp.ClientTimeout(total=30)) as response:
                response_time = time.time() - start_time
                status_code = response.status
                content = await response.text()
                page_size = len(content.encode('utf-8'))
                
                return {
                    'content': content,
                    'response_time': response_time,
                    'status_code': status_code,
                    'page_size': page_size
                }
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
            
            fetch_result = await self._fetch_page_async(session, url)
            
            if fetch_result is None:
                return {
                    'url': url,
                    'depth': depth,
                    'type': 'error',
                    'error': 'Failed to fetch or blocked by robots.txt',
                    'response_time': 0,
                    'status_code': 0,
                    'page_size': 0
                }
            
            html_content = fetch_result['content']
            response_time = fetch_result['response_time']
            status_code = fetch_result['status_code']
            page_size = fetch_result['page_size']
            
            # Use JavaScript rendering if enabled
            if self.use_js_rendering:
                rendered_content = await self._render_with_playwright(url)
                if rendered_content:
                    html_content = rendered_content
            
            # Parse HTML
            soup = BeautifulSoup(html_content, 'html.parser')
            page_text = self.extract_text(soup)
            
            # Content fingerprinting
            content_simhash = self._compute_simhash(page_text)
            if content_simhash is not None:
                self.content_hashes[url] = content_simhash
            
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
            
            # Extract links for graph building
            links = self.extract_links_advanced(html_content, url) if html_content else []
            
            result = None
            if text_match or name_match:
                result = {
                    'url': url,
                    'depth': depth,
                    'type': 'page',
                    'content_preview': page_text[:500] if page_text else '',
                    'matched_text': search_text if text_match else None,
                    'matched_name': search_names if name_match else None,
                    'content_hash': content_hash,
                    'links': links,
                    'response_time': response_time,
                    'status_code': status_code,
                    'page_size': page_size
                }
            else:
                # Store links even if page doesn't match search criteria
                result = {
                    'url': url,
                    'depth': depth,
                    'type': 'page',
                    'content_preview': page_text[:500] if page_text else '',
                    'content_hash': content_hash,
                    'links': links,
                    'response_time': response_time,
                    'status_code': status_code,
                    'page_size': page_size
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
                            fetch_result = await self._fetch_page_async(session, result['url'])
                            if fetch_result:
                                html_content = fetch_result['content']
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
                start_time = time.time()
                response = self.session.get(current_url, timeout=10)
                response_time = time.time() - start_time
                status_code = response.status_code
                page_size = len(response.content)
                
                response.raise_for_status()
                
                content_type = response.headers.get('content-type', '')
                
                if 'text/html' in content_type:
                    soup = BeautifulSoup(response.text, 'html.parser')
                    page_text = self.extract_text(soup)
                    
                    # Content fingerprinting
                    content_simhash = self._compute_simhash(page_text)
                    if content_simhash is not None:
                        self.content_hashes[current_url] = content_simhash
                    
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
                    
                    # Extract links for graph building
                    links = self.extract_links_advanced(response.text, current_url)
                    
                    if text_match or name_match:
                        result = {
                            'url': current_url,
                            'depth': current_depth,
                            'type': 'page',
                            'content_preview': page_text[:500] if page_text else '',
                            'matched_text': search_text if text_match else None,
                            'matched_name': search_names if name_match else None,
                            'content_hash': content_hash,
                            'links': links,
                            'response_time': response_time,
                            'status_code': status_code,
                            'page_size': page_size
                        }
                        self.results.append(result)
                    else:
                        # Store links even if page doesn't match search criteria
                        result = {
                            'url': current_url,
                            'depth': current_depth,
                            'type': 'page',
                            'content_preview': page_text[:500] if page_text else '',
                            'content_hash': content_hash,
                            'links': links,
                            'response_time': response_time,
                            'status_code': status_code,
                            'page_size': page_size
                        }
                        self.results.append(result)
                    
                    # Extract links for further crawling
                    if current_depth < self.depth:
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
                            'matched_extension': file_extensions if ext_match else None,
                            'response_time': response_time,
                            'status_code': status_code,
                            'page_size': page_size
                        }
                        self.results.append(result)
                
                if progress_callback:
                    progress_callback(len(self.visited_urls), len(self.results))
                    
            except requests.RequestException as e:
                result = {
                    'url': current_url,
                    'depth': current_depth,
                    'type': 'error',
                    'error': str(e),
                    'response_time': response_time if 'response_time' in locals() else 0,
                    'status_code': status_code if 'status_code' in locals() else 0,
                    'page_size': page_size if 'page_size' in locals() else 0
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
            url = f"https://crt.sh/?q=%.{domain}&exclude=expired&output=json"
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

class NetworkGraphGenerator:
    """Generate and visualize site structure using networkx + matplotlib."""
    
    def __init__(self):
        if nx is None or plt is None:
            raise ImportError("networkx and matplotlib are required for NetworkGraphGenerator")
        self.graph = nx.DiGraph()
        self.url_to_node = {}
        self.node_counter = 0
    
    def add_edge(self, source_url: str, target_url: str, edge_type: str = 'link'):
        """Add an edge between two URLs."""
        if source_url not in self.url_to_node:
            self.url_to_node[source_url] = f"n{self.node_counter}"
            self.graph.add_node(self.url_to_node[source_url], url=source_url)
            self.node_counter += 1
        
        if target_url not in self.url_to_node:
            self.url_to_node[target_url] = f"n{self.node_counter}"
            self.graph.add_node(self.url_to_node[target_url], url=target_url)
            self.node_counter += 1
        
        self.graph.add_edge(
            self.url_to_node[source_url], 
            self.url_to_node[target_url], 
            edge_type=edge_type
        )
    
    def build_from_crawl_results(self, crawl_results: List[Dict]):
        """Build graph from crawl results."""
        url_to_links = {}
        
        for result in crawl_results:
            url = result.get('url')
            if url and result.get('type') == 'page':
                url_to_links[url] = result.get('links', [])
        
        # Build edges
        for source, targets in url_to_links.items():
            for target in targets:
                self.add_edge(source, target)
    
    def calculate_metrics(self) -> Dict:
        """Calculate graph metrics."""
        if not self.graph.nodes():
            return {}
        
        metrics = {
            'num_nodes': self.graph.number_of_nodes(),
            'num_edges': self.graph.number_of_edges(),
            'density': nx.density(self.graph),
            'is_connected': nx.is_weakly_connected(self.graph),
        }
        
        if metrics['is_connected']:
            metrics['average_shortest_path'] = nx.average_shortest_path_length(self.graph)
        
        # Centrality measures
        try:
            metrics['pagerank'] = nx.pagerank(self.graph)
            metrics['betweenness'] = nx.betweenness_centrality(self.graph)
            metrics['degree_centrality'] = nx.degree_centrality(self.graph)
        except:
            pass
        
        return metrics
    
    def visualize(self, output_path: Optional[str] = None, figsize: tuple = (20, 15)):
        """Visualize the graph."""
        if not self.graph.nodes():
            print("No nodes in graph to visualize")
            return None
        
        plt.figure(figsize=figsize)
        
        # Use spring layout for better visualization
        pos = nx.spring_layout(self.graph, k=2, iterations=50)
        
        # Draw nodes
        nx.draw_networkx_nodes(self.graph, pos, node_size=500, node_color='lightblue', alpha=0.8)
        
        # Draw edges
        nx.draw_networkx_edges(self.graph, pos, edge_color='gray', alpha=0.5, arrows=True)
        
        # Draw labels (use shortened URLs)
        labels = {node: self.graph.nodes[node]['url'][:30] + '...' 
                  if len(self.graph.nodes[node]['url']) > 30 
                  else self.graph.nodes[node]['url'] 
                  for node in self.graph.nodes()}
        nx.draw_networkx_labels(self.graph, pos, labels, font_size=8)
        
        plt.title("Website Structure Graph")
        plt.axis('off')
        
        if output_path:
            plt.savefig(output_path, dpi=300, bbox_inches='tight')
            plt.close()
            return output_path
        else:
            plt.show()
            return None
    
    def get_figure_canvas(self, figsize: tuple = (20, 15)) -> Optional[FigureCanvas]:
        """Get matplotlib figure canvas for PyQt integration."""
        if plt is None:
            return None
        
        if not self.graph.nodes():
            return None
        
        fig = plt.figure(figsize=figsize)
        pos = nx.spring_layout(self.graph, k=2, iterations=50)
        
        nx.draw_networkx_nodes(self.graph, pos, node_size=500, node_color='lightblue', alpha=0.8)
        nx.draw_networkx_edges(self.graph, pos, edge_color='gray', alpha=0.5, arrows=True)
        
        labels = {node: self.graph.nodes[node]['url'][:30] + '...' 
                  if len(self.graph.nodes[node]['url']) > 30 
                  else self.graph.nodes[node]['url'] 
                  for node in self.graph.nodes()}
        nx.draw_networkx_labels(self.graph, pos, labels, font_size=8)
        
        plt.title("Website Structure Graph")
        plt.axis('off')
        
        canvas = FigureCanvas(fig)
        return canvas
    
    def export_graph(self, output_path: str, format: str = 'gexf'):
        """Export graph to file."""
        if format == 'gexf':
            nx.write_gexf(self.graph, output_path)
        elif format == 'graphml':
            nx.write_graphml(self.graph, output_path)
        elif format == 'json':
            from networkx.readwrite import json_graph
            data = json_graph.node_link_data(self.graph)
            import json
            with open(output_path, 'w') as f:
                json.dump(data, f)
        else:
            raise ValueError(f"Unsupported format: {format}")

class ContentClassifier:
    """Classify pages by topic/sentiment using BERT/transformer models."""
    
    def __init__(self, model_name: str = 'distilbert-base-uncased-finetuned-sst-2-english'):
        if pipeline is None:
            raise ImportError("transformers library is required for ContentClassifier")
        
        self.model_name = model_name
        self.classifier = None
        self.topic_classifier = None
        self._load_models()
    
    def _load_models(self):
        """Load classification models."""
        try:
            # Sentiment analysis
            self.classifier = pipeline('sentiment-analysis', model=self.model_name)
            
            # Topic classification (using zero-shot classification)
            self.topic_classifier = pipeline('zero-shot-classification')
        except Exception as e:
            print(f"Error loading models: {e}")
            self.classifier = None
            self.topic_classifier = None
    
    def classify_sentiment(self, text: str) -> Dict:
        """Classify sentiment of text."""
        if self.classifier is None:
            return {'error': 'Model not loaded'}
        
        try:
            result = self.classifier(text[:512])  # BERT has 512 token limit
            return {
                'label': result[0]['label'],
                'score': result[0]['score'],
                'text_preview': text[:100]
            }
        except Exception as e:
            return {'error': str(e)}
    
    def classify_topic(self, text: str, candidate_labels: List[str]) -> Dict:
        """Classify topic using zero-shot classification."""
        if self.topic_classifier is None:
            return {'error': 'Model not loaded'}
        
        try:
            result = self.topic_classifier(text[:512], candidate_labels)
            return {
                'top_topic': result['labels'][0],
                'confidence': result['scores'][0],
                'all_topics': list(zip(result['labels'], result['scores'])),
                'text_preview': text[:100]
            }
        except Exception as e:
            return {'error': str(e)}
    
    def batch_classify(self, texts: List[str], classify_type: str = 'sentiment', 
                      candidate_labels: Optional[List[str]] = None) -> List[Dict]:
        """Classify multiple texts."""
        results = []
        
        for text in texts:
            if classify_type == 'sentiment':
                result = self.classify_sentiment(text)
            elif classify_type == 'topic' and candidate_labels:
                result = self.classify_topic(text, candidate_labels)
            else:
                result = {'error': 'Invalid classification type or missing labels'}
            
            results.append(result)
        
        return results

class NamedEntityRecognizer:
    """Extract persons, orgs, locations, dates using spaCy."""
    
    def __init__(self, model_name: str = 'en_core_web_sm'):
        if spacy is None:
            raise ImportError("spacy library is required for NamedEntityRecognizer")
        
        self.model_name = model_name
        self.nlp = None
        self._load_model()
    
    def _load_model(self):
        """Load spaCy model."""
        try:
            self.nlp = spacy.load(self.model_name)
        except OSError:
            print(f"Model {self.model_name} not found. Please install it with: python -m spacy download {self.model_name}")
            self.nlp = None
    
    def extract_entities(self, text: str) -> Dict:
        """Extract named entities from text."""
        if self.nlp is None:
            return {'error': 'Model not loaded'}
        
        try:
            doc = self.nlp(text)
            
            entities = {
                'PERSON': [],
                'ORG': [],
                'GPE': [],  # Geopolitical entity (countries, cities, etc.)
                'LOC': [],  # Location
                'DATE': [],
                'TIME': [],
                'EMAIL': [],
                'PHONE': [],
                'URL': [],
                'MONEY': [],
                'CARDINAL': [],
                'ORDINAL': []
            }
            
            for ent in doc.ents:
                if ent.label_ in entities:
                    entities[ent.label_].append({
                        'text': ent.text,
                        'start': ent.start_char,
                        'end': ent.end_char,
                        'label': ent.label_
                    })
            
            return entities
        except Exception as e:
            return {'error': str(e)}
    
    def extract_custom_patterns(self, text: str, patterns: List[Dict]) -> List[Dict]:
        """Extract custom patterns using spaCy's EntityRuler."""
        if self.nlp is None:
            return []
        
        try:
            from spacy.pipeline import EntityRuler
            
            ruler = EntityRuler(self.nlp)
            ruler.add_patterns(patterns)
            self.nlp.add_pipe(ruler, before='ner')
            
            doc = self.nlp(text)
            matches = []
            
            for ent in doc.ents:
                matches.append({
                    'text': ent.text,
                    'label': ent.label_,
                    'start': ent.start_char,
                    'end': ent.end_char
                })
            
            # Remove the ruler to avoid affecting future processing
            self.nlp.remove_pipe('entity_ruler')
            
            return matches
        except Exception as e:
            print(f"Error extracting custom patterns: {e}")
            return []

class ContactHarvester:
    """Extract emails, phone numbers, social media handles using regex."""
    
    EMAIL_PATTERN = r'[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}'
    PHONE_PATTERN = r'(?:\+?1[-.\s]?)?\(?[0-9]{3}\)?[-.\s]?[0-9]{3}[-.\s]?[0-9]{4}'
    TWITTER_PATTERN = r'@[\w]{1,15}'
    LINKEDIN_PATTERN = r'linkedin\.com/in/[\w-]+'
    FACEBOOK_PATTERN = r'facebook\.com/[\w.]+'
    INSTAGRAM_PATTERN = r'instagram\.com/[\w.]+'
    GITHUB_PATTERN = r'github\.com/[\w-]+'
    
    def __init__(self):
        self.patterns = {
            'email': self.EMAIL_PATTERN,
            'phone': self.PHONE_PATTERN,
            'twitter': self.TWITTER_PATTERN,
            'linkedin': self.LINKEDIN_PATTERN,
            'facebook': self.FACEBOOK_PATTERN,
            'instagram': self.INSTAGRAM_PATTERN,
            'github': self.GITHUB_PATTERN
        }
    
    def extract_contacts(self, text: str, contact_types: Optional[List[str]] = None) -> Dict:
        """Extract contacts from text."""
        if contact_types is None:
            contact_types = list(self.patterns.keys())
        
        results = {}
        
        for contact_type in contact_types:
            if contact_type in self.patterns:
                pattern = self.patterns[contact_type]
                matches = re.findall(pattern, text, re.IGNORECASE)
                results[contact_type] = list(set(matches))  # Remove duplicates
        
        return results
    
    def extract_from_html(self, html_content: str) -> Dict:
        """Extract contacts from HTML content."""
        soup = BeautifulSoup(html_content, 'html.parser')
        
        # Extract from text content
        text = soup.get_text()
        results = self.extract_contacts(text)
        
        # Extract from mailto links
        mailto_links = soup.find_all('a', href=re.compile(r'^mailto:', re.IGNORECASE))
        emails = [link['href'].replace('mailto:', '') for link in mailto_links]
        results['email'].extend(emails)
        results['email'] = list(set(results['email']))
        
        # Extract from tel links
        tel_links = soup.find_all('a', href=re.compile(r'^tel:', re.IGNORECASE))
        phones = [link['href'].replace('tel:', '') for link in tel_links]
        results['phone'].extend(phones)
        results['phone'] = list(set(results['phone']))
        
        return results
    
    def add_custom_pattern(self, name: str, pattern: str):
        """Add a custom regex pattern."""
        self.patterns[name] = pattern

class TechnologyStackFingerprinter:
    """Detect CMS, JS frameworks, web servers, analytics (Wappalyzer-style)."""
    
    TECHNOLOGY_SIGNATURES = {
        'cms': {
            'WordPress': ['wp-content', 'wp-includes', '/wordpress/'],
            'Drupal': ['drupal', 'sites/default/files'],
            'Joomla': ['joomla', '/components/'],
            'Magento': ['magento', '/skin/'],
            'Shopify': ['shopify', 'cdn.shopify.com'],
            'Squarespace': ['squarespace', 'static1.squarespace.com'],
            'Wix': ['wix', 'static.wixstatic.com'],
        },
        'javascript_frameworks': {
            'React': ['react', 'react-dom', '_react'],
            'Vue.js': ['vue', 'Vue', 'v-if'],
            'Angular': ['angular', 'ng-app', 'ng-controller'],
            'jQuery': ['jquery', '$(', 'jQuery'],
            'Ember.js': ['ember', 'Ember'],
            'Backbone.js': ['backbone', 'Backbone'],
            'Svelte': ['svelte', 'Svelte'],
        },
        'web_servers': {
            'Apache': ['Apache', 'Server: Apache'],
            'Nginx': ['nginx', 'Server: nginx'],
            'IIS': ['IIS', 'Microsoft-IIS'],
            'Cloudflare': ['cloudflare', 'cf-ray'],
        },
        'analytics': {
            'Google Analytics': ['google-analytics.com', 'ga.js', 'gtag.js'],
            'Google Tag Manager': ['googletagmanager.com', 'GTM-'],
            'Hotjar': ['hotjar.com', 'hj'],
            'Mixpanel': ['mixpanel.com', 'mixpanel'],
            'Segment': ['segment.com', 'analytics.js'],
        },
        'cdn': {
            'Cloudflare': ['cloudflare', 'cf-ray'],
            'CloudFront': ['cloudfront.net'],
            'Akamai': ['akamai', 'akamaihd.net'],
            'Fastly': ['fastly', 'fastly.net'],
        }
    }
    
    def __init__(self):
        self.detected_technologies = {}
    
    def fingerprint(self, url: str, html_content: str, headers: Dict) -> Dict:
        """Fingerprint technology stack from URL, HTML, and headers."""
        results = {
            'cms': [],
            'javascript_frameworks': [],
            'web_servers': [],
            'analytics': [],
            'cdn': []
        }
        
        # Check headers
        server_header = headers.get('Server', '').lower()
        for tech, signatures in self.TECHNOLOGY_SIGNATURES['web_servers'].items():
            for sig in signatures:
                if sig.lower() in server_header:
                    if tech not in results['web_servers']:
                        results['web_servers'].append(tech)
        
        # Check HTML content
        html_lower = html_content.lower()
        
        for category, technologies in self.TECHNOLOGY_SIGNATURES.items():
            if category == 'web_servers':
                continue  # Already checked in headers
            
            for tech, signatures in technologies.items():
                for sig in signatures:
                    if sig.lower() in html_lower:
                        if tech not in results[category]:
                            results[category].append(tech)
        
        # Check URL patterns
        url_lower = url.lower()
        for tech, signatures in self.TECHNOLOGY_SIGNATURES['cms'].items():
            for sig in signatures:
                if sig.lower() in url_lower:
                    if tech not in results['cms']:
                        results['cms'].append(tech)
        
        self.detected_technologies = results
        return results
    
    def generate_report(self) -> str:
        """Generate a human-readable report."""
        if not self.detected_technologies:
            return "No technologies detected."
        
        report = "Technology Stack Detection Report\n"
        report += "=" * 40 + "\n\n"
        
        for category, technologies in self.detected_technologies.items():
            if technologies:
                report += f"{category.replace('_', ' ').title()}:\n"
                for tech in technologies:
                    report += f"  - {tech}\n"
                report += "\n"
        
        return report

class VisualAnalyzer:
    """Full-page screenshots + perceptual hashing for phishing/clone detection."""
    
    def __init__(self):
        if Image is None or imagehash is None:
            raise ImportError("PIL and imagehash are required for VisualAnalyzer")
        self.screenshot_dir = "screenshots"
        self.hash_database = {}
    
    def capture_screenshot(self, url: str, output_path: Optional[str] = None) -> Optional[str]:
        """Capture screenshot using Playwright."""
        if async_playwright is None:
            print("Playwright is required for screenshot capture")
            return None
        
        import asyncio
        
        async def _capture():
            async with async_playwright() as p:
                browser = await p.chromium.launch(headless=True)
                page = await browser.new_page()
                await page.goto(url, wait_until='networkidle', timeout=30000)
                
                if output_path is None:
                    import os
                    os.makedirs(self.screenshot_dir, exist_ok=True)
                    filename = f"{hashlib.md5(url.encode()).hexdigest()}.png"
                    output_path = os.path.join(self.screenshot_dir, filename)
                
                await page.screenshot(path=output_path, full_page=True)
                await browser.close()
                return output_path
        
        try:
            return asyncio.run(_capture())
        except Exception as e:
            print(f"Error capturing screenshot: {e}")
            return None
    
    def compute_perceptual_hash(self, image_path: str) -> Optional[str]:
        """Compute perceptual hash of an image."""
        try:
            image = Image.open(image_path)
            phash = imagehash.phash(image)
            return str(phash)
        except Exception as e:
            print(f"Error computing perceptual hash: {e}")
            return None
    
    def detect_clone(self, image_path: str, threshold: int = 5) -> List[Dict]:
        """Detect if image is a clone of any in database."""
        current_hash = self.compute_perceptual_hash(image_path)
        if current_hash is None:
            return []
        
        clones = []
        
        for url, stored_hash in self.hash_database.items():
            hash1 = imagehash.hex_to_hash(current_hash)
            hash2 = imagehash.hex_to_hash(stored_hash)
            distance = hash1 - hash2
            
            if distance <= threshold:
                clones.append({
                    'url': url,
                    'hash': stored_hash,
                    'distance': distance
                })
        
        return clones
    
    def add_to_database(self, url: str, image_path: str):
        """Add image hash to database."""
        phash = self.compute_perceptual_hash(image_path)
        if phash:
            self.hash_database[url] = phash
    
    def compare_images(self, image_path1: str, image_path2: str) -> Dict:
        """Compare two images using perceptual hashing."""
        hash1 = self.compute_perceptual_hash(image_path1)
        hash2 = self.compute_perceptual_hash(image_path2)
        
        if hash1 is None or hash2 is None:
            return {'error': 'Could not compute hashes'}
        
        h1 = imagehash.hex_to_hash(hash1)
        h2 = imagehash.hex_to_hash(hash2)
        distance = h1 - h2
        
        return {
            'hash1': hash1,
            'hash2': hash2,
            'distance': distance,
            'is_similar': distance <= 5
        }

class OCREngine:
    """Extract text from images using Tesseract OCR."""
    
    def __init__(self, tesseract_path: Optional[str] = None):
        if pytesseract is None:
            raise ImportError("pytesseract is required for OCREngine")
        
        if tesseract_path:
            pytesseract.pytesseract.tesseract_cmd = tesseract_path
        
        self.supported_languages = ['eng', 'spa', 'fra', 'deu', 'ita', 'por']
    
    def extract_text(self, image_path: str, language: str = 'eng') -> str:
        """Extract text from image."""
        try:
            text = pytesseract.image_to_string(Image.open(image_path), lang=language)
            return text
        except Exception as e:
            return f"Error: {str(e)}"
    
    def extract_text_with_boxes(self, image_path: str, language: str = 'eng') -> List[Dict]:
        """Extract text with bounding box information."""
        try:
            data = pytesseract.image_to_data(Image.open(image_path), lang=language, output_type=pytesseract.Output.DICT)
            
            results = []
            n_boxes = len(data['text'])
            
            for i in range(n_boxes):
                if int(data['conf'][i]) > 60:  # Confidence threshold
                    results.append({
                        'text': data['text'][i],
                        'confidence': data['conf'][i],
                        'bbox': {
                            'left': data['left'][i],
                            'top': data['top'][i],
                            'width': data['width'][i],
                            'height': data['height'][i]
                        }
                    })
            
            return results
        except Exception as e:
            return [{'error': str(e)}]
    
    def extract_from_url(self, image_url: str, language: str = 'eng') -> str:
        """Extract text from image URL."""
        try:
            response = requests.get(image_url, timeout=10)
            response.raise_for_status()
            
            from io import BytesIO
            image = Image.open(BytesIO(response.content))
            text = pytesseract.image_to_string(image, lang=language)
            return text
        except Exception as e:
            return f"Error: {str(e)}"

class TemporalAnalyzer:
    """Diff-tracking (textual & visual) with alert triggers on regex patterns."""
    
    def __init__(self, storage_dir: str = "temporal_data"):
        self.storage_dir = storage_dir
        os.makedirs(storage_dir, exist_ok=True)
        self.baseline_data = {}
    
    def capture_baseline(self, url: str, content: str, metadata: Optional[Dict] = None):
        """Capture baseline data for comparison."""
        timestamp = datetime.now().isoformat()
        
        baseline = {
            'url': url,
            'timestamp': timestamp,
            'content_hash': hashlib.sha256(content.encode()).hexdigest(),
            'content': content,
            'metadata': metadata or {}
        }
        
        # Store baseline
        key = hashlib.md5(url.encode()).hexdigest()
        self.baseline_data[key] = baseline
        
        # Save to disk
        baseline_path = os.path.join(self.storage_dir, f"{key}_baseline.json")
        with open(baseline_path, 'w', encoding='utf-8') as f:
            json.dump(baseline, f, indent=2)
        
        return baseline
    
    def detect_changes(self, url: str, current_content: str, 
                      alert_patterns: Optional[List[str]] = None) -> Dict:
        """Detect changes from baseline."""
        key = hashlib.md5(url.encode()).hexdigest()
        
        if key not in self.baseline_data:
            return {'error': 'No baseline found for this URL'}
        
        baseline = self.baseline_data[key]
        current_hash = hashlib.sha256(current_content.encode()).hexdigest()
        
        changes = {
            'url': url,
            'timestamp': datetime.now().isoformat(),
            'baseline_timestamp': baseline['timestamp'],
            'content_changed': current_hash != baseline['content_hash'],
            'content_hash': current_hash,
            'baseline_hash': baseline['content_hash']
        }
        
        if changes['content_changed']:
            # Compute text diff
            changes['text_diff'] = self._compute_diff(baseline['content'], current_content)
            
            # Check for alert patterns
            if alert_patterns:
                changes['pattern_matches'] = self._check_patterns(current_content, alert_patterns)
        
        return changes
    
    def _compute_diff(self, old_text: str, new_text: str) -> Dict:
        """Compute text diff using difflib."""
        import difflib
        
        diff = difflib.unified_diff(
            old_text.splitlines(keepends=True),
            new_text.splitlines(keepends=True),
            fromfile='baseline',
            tofile='current'
        )
        
        return {
            'added_lines': 0,
            'removed_lines': 0,
            'diff': ''.join(diff)
        }
    
    def _check_patterns(self, content: str, patterns: List[str]) -> List[Dict]:
        """Check if content matches any alert patterns."""
        matches = []
        
        for pattern in patterns:
            try:
                regex_matches = re.finditer(pattern, content, re.IGNORECASE)
                for match in regex_matches:
                    matches.append({
                        'pattern': pattern,
                        'match': match.group(),
                        'position': match.start()
                    })
            except re.error:
                pass
        
        return matches
    
    def get_history(self, url: str) -> List[Dict]:
        """Get change history for a URL."""
        key = hashlib.md5(url.encode()).hexdigest()
        
        # Load history from disk
        history_files = [f for f in os.listdir(self.storage_dir) if f.startswith(key)]
        
        history = []
        for hist_file in history_files:
            hist_path = os.path.join(self.storage_dir, hist_file)
            try:
                with open(hist_path, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                    history.append(data)
            except:
                pass
        
        return sorted(history, key=lambda x: x.get('timestamp', ''))

class StatisticalAnalyzer:
    """Generate reports on response times, status codes, content types, outbound links."""
    
    def __init__(self):
        self.metrics = {
            'response_times': [],
            'status_codes': {},
            'content_types': {},
            'outbound_links': [],
            'page_sizes': []
        }
    
    def record_metric(self, url: str, response_time: float, status_code: int, 
                      content_type: str, page_size: int, outbound_links: List[str]):
        """Record a single metric."""
        self.metrics['response_times'].append(response_time)
        
        if status_code not in self.metrics['status_codes']:
            self.metrics['status_codes'][status_code] = 0
        self.metrics['status_codes'][status_code] += 1
        
        if content_type not in self.metrics['content_types']:
            self.metrics['content_types'][content_type] = 0
        self.metrics['content_types'][content_type] += 1
        
        self.metrics['page_sizes'].append(page_size)
        self.metrics['outbound_links'].extend(outbound_links)
    
    def generate_summary(self) -> Dict:
        """Generate statistical summary."""
        if not self.metrics['response_times']:
            return {'error': 'No metrics recorded'}
        
        summary = {
            'response_times': {
                'mean': np.mean(self.metrics['response_times']) if np else sum(self.metrics['response_times']) / len(self.metrics['response_times']),
                'median': np.median(self.metrics['response_times']) if np else sorted(self.metrics['response_times'])[len(self.metrics['response_times']) // 2],
                'min': min(self.metrics['response_times']),
                'max': max(self.metrics['response_times']),
                'std_dev': np.std(self.metrics['response_times']) if np else 0
            },
            'status_codes': self.metrics['status_codes'],
            'content_types': self.metrics['content_types'],
            'page_sizes': {
                'mean': np.mean(self.metrics['page_sizes']) if np else sum(self.metrics['page_sizes']) / len(self.metrics['page_sizes']),
                'total': sum(self.metrics['page_sizes']),
                'min': min(self.metrics['page_sizes']),
                'max': max(self.metrics['page_sizes'])
            },
            'outbound_links': {
                'total': len(self.metrics['outbound_links']),
                'unique': len(set(self.metrics['outbound_links']))
            },
            'total_requests': len(self.metrics['response_times'])
        }
        
        return summary
    
    def generate_report(self) -> str:
        """Generate human-readable report."""
        summary = self.generate_summary()
        
        if 'error' in summary:
            return summary['error']
        
        report = "Statistical Analysis Report\n"
        report += "=" * 40 + "\n\n"
        
        report += f"Total Requests: {summary['total_requests']}\n\n"
        
        report += "Response Times:\n"
        rt = summary['response_times']
        report += f"  Mean: {rt['mean']:.3f}s\n"
        report += f"  Median: {rt['median']:.3f}s\n"
        report += f"  Min: {rt['min']:.3f}s\n"
        report += f"  Max: {rt['max']:.3f}s\n"
        report += f"  Std Dev: {rt['std_dev']:.3f}s\n\n"
        
        report += "Status Codes:\n"
        for code, count in summary['status_codes'].items():
            report += f"  {code}: {count}\n"
        report += "\n"
        
        report += "Content Types:\n"
        for ct, count in summary['content_types'].items():
            report += f"  {ct}: {count}\n"
        report += "\n"
        
        report += "Page Sizes:\n"
        ps = summary['page_sizes']
        report += f"  Mean: {ps['mean']:.0f} bytes\n"
        report += f"  Total: {ps['total']:.0f} bytes\n"
        report += f"  Min: {ps['min']} bytes\n"
        report += f"  Max: {ps['max']} bytes\n\n"
        
        report += "Outbound Links:\n"
        report += f"  Total: {summary['outbound_links']['total']}\n"
        report += f"  Unique: {summary['outbound_links']['unique']}\n"
        
        return report

class IPGeolocation:
    """IP Geolocation & ASN Mapping with map visualization."""
    
    def __init__(self, geoip_db_path: Optional[str] = None):
        self.geoip_db_path = geoip_db_path
        self.reader = None
        self.cache = {}
        self.using_fallback = False
        
        if geoip2 and geoip_db_path:
            try:
                import os
                if not os.path.exists(geoip_db_path):
                    print(f"Warning: GeoIP database file not found at {geoip_db_path}. Using fallback API.")
                    self.using_fallback = True
                else:
                    self.reader = geoip2.database.Reader(geoip_db_path)
            except Exception as e:
                print(f"Failed to load GeoIP database: {e}. Using fallback API.")
                self.using_fallback = True
    
    def geolocate_ip(self, ip: str) -> Dict:
        """Geolocate an IP address."""
        if ip in self.cache:
            return self.cache[ip]
        
        result = {
            'ip': ip,
            'country': None,
            'city': None,
            'latitude': None,
            'longitude': None,
            'asn': None,
            'org': None,
            'error': None
        }
        
        try:
            # Use ipinfo.io API as fallback
            response = requests.get(f"https://ipinfo.io/{ip}/json", timeout=5)
            response.raise_for_status()
            data = response.json()
            
            result['country'] = data.get('country')
            result['city'] = data.get('city')
            result['org'] = data.get('org')
            result['asn'] = data.get('org', '').split(' ')[0] if data.get('org') else None
            
            # Parse coordinates
            loc = data.get('loc', '')
            if loc:
                lat, lon = loc.split(',')
                result['latitude'] = float(lat)
                result['longitude'] = float(lon)
            
            # Try GeoIP database if available
            if self.reader:
                try:
                    response = self.reader.city(ip)
                    result['country'] = response.country.iso_code
                    result['city'] = response.city.name
                    result['latitude'] = response.location.latitude
                    result['longitude'] = response.location.longitude
                    result['asn'] = response.network
                    result['org'] = response.network
                except:
                    pass
        
        except Exception as e:
            result['error'] = str(e)
        
        self.cache[ip] = result
        return result
    
    def batch_geolocate(self, ips: List[str]) -> Dict[str, Dict]:
        """Geolocate multiple IPs."""
        results = {}
        for ip in ips:
            results[ip] = self.geolocate_ip(ip)
        return results
    
    def generate_map(self, ip_data: List[Dict], output_path: str = "geolocation_map.html") -> Optional[str]:
        """Generate interactive map using folium."""
        if folium is None:
            print("folium library not available")
            return None
        
        try:
            m = folium.Map(location=[20, 0], zoom_start=2)
            
            for data in ip_data:
                if data.get('latitude') and data.get('longitude'):
                    popup_text = f"""
                    <b>IP:</b> {data['ip']}<br>
                    <b>Country:</b> {data.get('country', 'N/A')}<br>
                    <b>City:</b> {data.get('city', 'N/A')}<br>
                    <b>ASN:</b> {data.get('asn', 'N/A')}<br>
                    <b>Organization:</b> {data.get('org', 'N/A')}
                    """
                    folium.Marker(
                        [data['latitude'], data['longitude']],
                        popup=folium.Popup(popup_text, max_width=300)
                    ).add_to(m)
            
            m.save(output_path)
            return output_path
        except Exception as e:
            print(f"Error generating map: {e}")
            return None

class SSLTLSAnalyzer:
    """SSL/TLS Cipher Analysis - certificates, HSTS, CSP headers.
    
    SECURITY NOTE: This analyzer disables hostname verification (check_hostname=False) and 
    certificate verification (verify_mode=ssl.CERT_NONE) when retrieving certificates. 
    This is intentional for certificate analysis purposes only, as it allows inspection of 
    certificates even when they have hostname mismatches or other verification issues.
    
    WARNING: This configuration should NOT be used for general HTTPS requests, as it 
    exposes the application to man-in-the-middle attacks. The disabled verification is 
    only used for the specific certificate inspection functionality in analyze_certificate().
    All other HTTP requests use default SSL verification.
    """
    
    WEAK_CIPHERS = [
        'RC4', 'DES', '3DES', 'MD5', 'SHA1', 'NULL', 'EXPORT', 'anon'
    ]
    
    def __init__(self):
        self.session = requests.Session()
        self.session.headers.update({
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
        })
    
    def analyze_certificate(self, hostname: str, port: int = 443) -> Dict:
        """Analyze SSL/TLS certificate.
        
        SECURITY NOTE: This method intentionally disables SSL verification to allow
        certificate inspection even for certificates with hostname mismatches or
        other verification issues. This is safe for analysis purposes but should
        not be used for secure data transmission.
        """
        result = {
            'hostname': hostname,
            'port': port,
            'issuer': None,
            'subject': None,
            'version': None,
            'serial': None,
            'not_before': None,
            'not_after': None,
            'is_valid': None,
            'days_until_expiry': None,
            'signature_algorithm': None,
            'key_size': None,
            'weak_cipher': False,
            'error': None,
            'verification_disabled': True  # Document that verification is disabled
        }
        
        try:
            # Get certificate from socket
            import socket
            context = ssl.create_default_context()
            # WARNING: Verification disabled for certificate analysis purposes
            context.check_hostname = False
            context.verify_mode = ssl.CERT_NONE
            
            with socket.create_connection((hostname, port), timeout=10) as sock:
                with context.wrap_socket(sock, server_hostname=hostname) as ssock:
                    cert = ssock.getpeercert()
                    
                    result['version'] = ssock.version()
                    result['cipher'] = ssock.cipher()
                    result['weak_cipher'] = any(weak in str(ssock.cipher()).upper() 
                                              for weak in self.WEAK_CIPHERS)
                    
                    # Parse certificate
                    result['issuer'] = dict(x[0] for x in cert.get('issuer', []))
                    result['subject'] = dict(x[0] for x in cert.get('subject', []))
                    result['serial'] = cert.get('serialNumber')
                    result['not_before'] = cert.get('notBefore')
                    result['not_after'] = cert.get('notAfter')
                    result['signature_algorithm'] = cert.get('signatureAlgorithm')
                    
                    # Check validity
                    from datetime import datetime
                    not_after = datetime.strptime(cert['notAfter'], '%b %d %H:%M:%S %Y %Z')
                    days_left = (not_after - datetime.utcnow()).days
                    result['days_until_expiry'] = days_left
                    result['is_valid'] = days_left > 0
        
        except Exception as e:
            result['error'] = str(e)
        
        return result
    
    def check_security_headers(self, url: str) -> Dict:
        """Check for security headers (HSTS, CSP, etc.)."""
        result = {
            'url': url,
            'headers': {},
            'security_headers': {
                'Strict-Transport-Security': None,
                'Content-Security-Policy': None,
                'X-Frame-Options': None,
                'X-Content-Type-Options': None,
                'X-XSS-Protection': None,
                'Referrer-Policy': None,
                'Permissions-Policy': None
            },
            'missing_headers': [],
            'error': None
        }
        
        try:
            response = self.session.get(url, timeout=10)
            result['headers'] = dict(response.headers)
            
            for header in result['security_headers']:
                result['security_headers'][header] = response.headers.get(header)
                if not response.headers.get(header):
                    result['missing_headers'].append(header)
        
        except Exception as e:
            result['error'] = str(e)
        
        return result
    
    def full_analysis(self, url: str) -> Dict:
        """Perform full SSL/TLS and security header analysis."""
        from urllib.parse import urlparse
        parsed = urlparse(url)
        hostname = parsed.netloc.split(':')[0]
        
        cert_analysis = self.analyze_certificate(hostname)
        header_analysis = self.check_security_headers(url)
        
        return {
            'certificate': cert_analysis,
            'security_headers': header_analysis
        }

class TracerouteAnalyzer:
    """Traceroute & Latency Metrics from multiple geographic proxies."""
    
    GEOGRAPHIC_ENDPOINTS = {
        'US-East': 'https://httpbin.org/ip',
        'US-West': 'https://httpbin.org/ip',
        'Europe': 'https://httpbin.org/ip',
        'Asia': 'https://httpbin.org/ip',
        'South America': 'https://httpbin.org/ip'
    }
    
    def __init__(self):
        self.session = requests.Session()
        self.session.headers.update({
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
        })
    
    def measure_latency(self, target: str, num_pings: int = 4) -> Dict:
        """Measure latency to target."""
        latencies = []
        
        for _ in range(num_pings):
            try:
                start_time = time.time()
                response = self.session.get(target, timeout=10)
                end_time = time.time()
                latencies.append((end_time - start_time) * 1000)  # Convert to ms
            except Exception as e:
                pass
        
        if not latencies:
            return {'error': 'Failed to measure latency'}
        
        return {
            'target': target,
            'latency_ms': {
                'min': min(latencies),
                'max': max(latencies),
                'avg': sum(latencies) / len(latencies),
                'median': sorted(latencies)[len(latencies) // 2]
            },
            'packet_loss': (num_pings - len(latencies)) / num_pings * 100
        }
    
    def traceroute(self, target: str, max_hops: int = 30) -> List[Dict]:
        """Perform traceroute (simplified - uses HTTP hops)."""
        results = []
        
        try:
            # This is a simplified traceroute using HTTP requests
            # For full ICMP traceroute, you'd need raw socket access (admin privileges)
            hostname = socket.gethostbyname(target)
            
            for ttl in range(1, max_hops + 1):
                try:
                    start_time = time.time()
                    response = self.session.get(f"http://{target}", timeout=5)
                    rtt = (time.time() - start_time) * 1000
                    
                    results.append({
                        'hop': ttl,
                        'ip': hostname,
                        'rtt_ms': rtt,
                        'status': 'success'
                    })
                    break  # Reached target
                except requests.RequestException:
                    results.append({
                        'hop': ttl,
                        'ip': '*',
                        'rtt_ms': None,
                        'status': 'timeout'
                    })
        
        except Exception as e:
            results.append({'error': str(e)})
        
        return results
    
    def multi_region_latency(self, target: str) -> Dict:
        """Measure latency from multiple geographic regions."""
        results = {}
        
        for region, endpoint in self.GEOGRAPHIC_ENDPOINTS.items():
            try:
                latency = self.measure_latency(endpoint)
                results[region] = latency
            except Exception as e:
                results[region] = {'error': str(e)}
        
        return results

class VulnerabilityScanner:
    """Basic Vulnerability Scanning - .git, .env, admin panels, security headers."""
    
    COMMON_VULNERABLE_PATHS = [
        '.git/',
        '.git/config',
        '.env',
        '.env.local',
        '.env.production',
        'wp-config.php',
        'config.php',
        'admin/',
        'administrator/',
        'login/',
        'wp-admin/',
        'phpmyadmin/',
        'console/',
        'dashboard/',
        'debug/',
        'test/',
        'backup/',
        'backups/',
        '.svn/',
        '.DS_Store',
        'web.config',
        '.htaccess',
        'robots.txt'
    ]
    
    SECURITY_HEADERS = [
        'Strict-Transport-Security',
        'Content-Security-Policy',
        'X-Frame-Options',
        'X-Content-Type-Options',
        'X-XSS-Protection',
        'Referrer-Policy'
    ]
    
    def __init__(self):
        self.session = requests.Session()
        self.session.headers.update({
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
        })
    
    def scan_exposed_files(self, base_url: str) -> List[Dict]:
        """Scan for exposed sensitive files."""
        from urllib.parse import urljoin
        vulnerabilities = []
        
        for path in self.COMMON_VULNERABLE_PATHS:
            url = urljoin(base_url, path)
            
            try:
                response = self.session.get(url, timeout=5)
                
                if response.status_code == 200:
                    vulnerabilities.append({
                        'type': 'exposed_file',
                        'path': path,
                        'url': url,
                        'status_code': response.status_code,
                        'content_length': len(response.content),
                        'severity': 'high' if path in ['.env', '.git/config', 'wp-config.php'] else 'medium'
                    })
                elif response.status_code == 403:
                    vulnerabilities.append({
                        'type': 'forbidden_path',
                        'path': path,
                        'url': url,
                        'status_code': response.status_code,
                        'severity': 'low'
                    })
            
            except requests.RequestException:
                pass
        
        return vulnerabilities
    
    def scan_security_headers(self, url: str) -> Dict:
        """Check for missing security headers."""
        try:
            response = self.session.get(url, timeout=10)
            headers = dict(response.headers)
            
            missing = []
            present = {}
            
            for header in self.SECURITY_HEADERS:
                if header in headers:
                    present[header] = headers[header]
                else:
                    missing.append(header)
            
            return {
                'url': url,
                'present_headers': present,
                'missing_headers': missing,
                'security_score': len(present) / len(self.SECURITY_HEADERS) * 100
            }
        
        except Exception as e:
            return {'error': str(e)}
    
    def scan_admin_panels(self, base_url: str) -> List[Dict]:
        """Scan for exposed admin panels."""
        from urllib.parse import urljoin
        admin_paths = ['admin', 'administrator', 'login', 'wp-admin', 'dashboard', 'console']
        found_panels = []
        
        for path in admin_paths:
            url = urljoin(base_url, path)
            
            try:
                response = self.session.get(url, timeout=5)
                
                if response.status_code == 200:
                    # Check if it looks like a login page
                    content = response.text.lower()
                    if 'login' in content or 'password' in content or 'username' in content:
                        found_panels.append({
                            'type': 'admin_panel',
                            'path': path,
                            'url': url,
                            'status_code': response.status_code,
                            'severity': 'medium'
                        })
            
            except requests.RequestException:
                pass
        
        return found_panels
    
    def full_scan(self, url: str) -> Dict:
        """Perform full vulnerability scan."""
        from urllib.parse import urlparse
        base_url = f"{urlparse(url).scheme}://{urlparse(url).netloc}"
        
        return {
            'exposed_files': self.scan_exposed_files(base_url),
            'security_headers': self.scan_security_headers(url),
            'admin_panels': self.scan_admin_panels(base_url)
        }

class SocialMediaSearcher:
    """Social Media/Forum Integration - Reddit, Mastodon API searches."""
    
    def __init__(self, reddit_client_id: Optional[str] = None, 
                 reddit_client_secret: Optional[str] = None,
                 mastodon_instance: Optional[str] = None,
                 mastodon_token: Optional[str] = None):
        self.reddit_client_id = reddit_client_id
        self.reddit_client_secret = reddit_client_secret
        self.mastodon_instance = mastodon_instance
        self.mastodon_token = mastodon_token
        
        self.reddit_client = None
        self.mastodon_client = None
        
        if praw and reddit_client_id and reddit_client_secret:
            try:
                self.reddit_client = praw.Reddit(
                    client_id=reddit_client_id,
                    client_secret=reddit_client_secret,
                    user_agent='ReconTool/1.0'
                )
            except:
                pass
        
        if mastodon and mastodon_instance and mastodon_token:
            try:
                self.mastodon_client = mastodon.Mastodon(
                    access_token=mastodon_token,
                    api_base_url=mastodon_instance
                )
            except:
                pass
    
    def search_reddit(self, query: str, limit: int = 10) -> List[Dict]:
        """Search Reddit for mentions."""
        if not self.reddit_client:
            return [{'error': 'Reddit client not configured'}]
        
        results = []
        
        try:
            # Search submissions
            for submission in self.reddit_client.subreddit('all').search(query, limit=limit):
                results.append({
                    'platform': 'reddit',
                    'type': 'submission',
                    'title': submission.title,
                    'url': submission.url,
                    'permalink': f"https://reddit.com{submission.permalink}",
                    'author': str(submission.author),
                    'score': submission.score,
                    'created_utc': submission.created_utc,
                    'num_comments': submission.num_comments
                })
        
        except Exception as e:
            results.append({'error': str(e)})
        
        return results
    
    def search_mastodon(self, query: str, limit: int = 10) -> List[Dict]:
        """Search Mastodon for mentions."""
        if not self.mastodon_client:
            return [{'error': 'Mastodon client not configured'}]
        
        results = []
        
        try:
            # Search for toots
            results_data = self.mastodon_client.search_v2(query, limit=limit)
            
            for result in results_data['statuses']:
                results.append({
                    'platform': 'mastodon',
                    'type': 'toot',
                    'content': result['content'],
                    'url': result['url'],
                    'account': result['account']['url'],
                    'created_at': result['created_at'],
                    'reblogs_count': result['reblogs_count'],
                    'favourites_count': result['favourites_count']
                })
        
        except Exception as e:
            results.append({'error': str(e)})
        
        return results
    
    def search_all(self, query: str, limit: int = 10) -> Dict[str, List[Dict]]:
        """Search all configured platforms."""
        results = {}
        
        if self.reddit_client:
            results['reddit'] = self.search_reddit(query, limit)
        
        if self.mastodon_client:
            results['mastodon'] = self.search_mastodon(query, limit)
        
        return results

class BacklinkDiscovery:
    """Backlink Discovery - CommonCrawl integration."""
    
    COMMONCRAWL_INDEX_API = "https://index.commoncrawl.org/cdx?url={url}&output=json"
    
    def __init__(self):
        self.session = requests.Session()
        self.session.headers.update({
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
        })
    
    def discover_backlinks(self, target_url: str) -> List[Dict]:
        """Discover backlinks using CommonCrawl index."""
        backlinks = []
        
        try:
            # Query CommonCrawl index
            encoded_url = requests.utils.quote(target_url)
            index_url = self.COMMONCRAWL_INDEX_API.format(url=encoded_url)
            
            response = self.session.get(index_url, timeout=30)
            response.raise_for_status()
            
            for line in response.text.strip().split('\n'):
                if line:
                    try:
                        data = json.loads(line)
                        if len(data) > 4:  # Valid CDX record
                            backlinks.append({
                                'url': data[0],
                                'timestamp': data[1],
                                'status': data[2],
                                'content_type': data[3],
                                'archive_url': f"https://web.archive.org/web/{data[1]}/{data[0]}"
                            })
                    except:
                        pass
        
        except Exception as e:
            return [{'error': str(e)}]
        
        return backlinks
    
    def analyze_backlinks(self, backlinks: List[Dict]) -> Dict:
        """Analyze backlink data."""
        if not backlinks or 'error' in backlinks[0]:
            return {'error': 'No valid backlinks'}
        
        unique_domains = set()
        status_codes = {}
        content_types = {}
        
        for bl in backlinks:
            try:
                from urllib.parse import urlparse
                domain = urlparse(bl['url']).netloc
                unique_domains.add(domain)
                
                status = bl.get('status', 'unknown')
                status_codes[status] = status_codes.get(status, 0) + 1
                
                ct = bl.get('content_type', 'unknown')
                content_types[ct] = content_types.get(ct, 0) + 1
            except:
                pass
        
        return {
            'total_backlinks': len(backlinks),
            'unique_domains': len(unique_domains),
            'domains': list(unique_domains),
            'status_codes': status_codes,
            'content_types': content_types
        }

class PassiveOSINT:
    """Passive OSINT Correlation - Shodan, Censys, VirusTotal, AbuseIPDB."""
    
    def __init__(self, shodan_api_key: Optional[str] = None,
                 censys_api_id: Optional[str] = None,
                 censys_api_secret: Optional[str] = None,
                 virustotal_api_key: Optional[str] = None,
                 abuseipdb_api_key: Optional[str] = None):
        self.shodan_api_key = shodan_api_key
        self.censys_api_id = censys_api_id
        self.censys_api_secret = censys_api_secret
        self.virustotal_api_key = virustotal_api_key
        self.abuseipdb_api_key = abuseipdb_api_key
        
        self.session = requests.Session()
        self.session.headers.update({
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
        })
    
    def query_shodan(self, target: str) -> Dict:
        """Query Shodan for host information."""
        if not self.shodan_api_key:
            return {'error': 'Shodan API key not configured'}
        
        try:
            response = self.session.get(
                f"https://api.shodan.io/shodan/host/{target}?key={self.shodan_api_key}",
                timeout=10
            )
            response.raise_for_status()
            return response.json()
        except Exception as e:
            return {'error': str(e)}
    
    def query_censys(self, target: str) -> Dict:
        """Query Censys for host information."""
        if not self.censys_api_id or not self.censys_api_secret:
            return {'error': 'Censys API credentials not configured'}
        
        try:
            response = self.session.get(
                f"https://search.censys.io/api/v2/hosts/{target}",
                auth=(self.censys_api_id, self.censys_api_secret),
                timeout=10
            )
            response.raise_for_status()
            return response.json()
        except Exception as e:
            return {'error': str(e)}
    
    def query_virustotal(self, ip: str) -> Dict:
        """Query VirusTotal for IP reputation."""
        if not self.virustotal_api_key:
            return {'error': 'VirusTotal API key not configured'}
        
        try:
            response = self.session.get(
                f"https://www.virustotal.com/api/v3/ip_addresses/{ip}",
                headers={'x-apikey': self.virustotal_api_key},
                timeout=10
            )
            response.raise_for_status()
            return response.json()
        except Exception as e:
            return {'error': str(e)}
    
    def query_abuseipdb(self, ip: str) -> Dict:
        """Query AbuseIPDB for IP reputation."""
        if not self.abuseipdb_api_key:
            return {'error': 'AbuseIPDB API key not configured'}
        
        try:
            response = self.session.get(
                f"https://api.abuseipdb.com/api/v2/check",
                headers={'Key': self.abuseipdb_api_key},
                params={'ipAddress': ip, 'maxAgeInDays': 90},
                timeout=10
            )
            response.raise_for_status()
            return response.json()
        except Exception as e:
            return {'error': str(e)}
    
    def correlate_osint(self, target: str) -> Dict:
        """Correlate OSINT data from multiple sources."""
        results = {}
        
        # Try to determine if target is IP or domain
        try:
            ipaddress.ip_address(target)
            is_ip = True
        except:
            is_ip = False
        
        if is_ip:
            results['shodan'] = self.query_shodan(target)
            results['virustotal'] = self.query_virustotal(target)
            results['abuseipdb'] = self.query_abuseipdb(target)
        else:
            results['censys'] = self.query_censys(target)
        
        return results

class KnowledgeGraphLinker:
    """Cross-Referencing with Knowledge Graphs - Wikidata, DBpedia."""
    
    WIKIDATA_API = "https://www.wikidata.org/w/api.php"
    DBPEDIA_SPARQL = "https://dbpedia.org/sparql"
    
    def __init__(self, use_ner: bool = True):
        self.session = requests.Session()
        self.session.headers.update({
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
        })
        self.ner = None
        if use_ner:
            try:
                self.ner = NamedEntityRecognizer()
            except (ImportError, OSError):
                # spaCy not available or model not installed, will use fallback
                pass
    
    def search_wikidata(self, query: str) -> List[Dict]:
        """Search Wikidata for entities."""
        results = []
        
        try:
            params = {
                'action': 'wbsearchentities',
                'search': query,
                'format': 'json',
                'language': 'en',
                'limit': 10
            }
            
            response = self.session.get(self.WIKIDATA_API, params=params, timeout=10)
            response.raise_for_status()
            
            data = response.json()
            
            for entity in data.get('search', []):
                results.append({
                    'id': entity['id'],
                    'label': entity['label'],
                    'description': entity.get('description', ''),
                    'url': f"https://www.wikidata.org/wiki/{entity['id']}"
                })
        
        except Exception as e:
            return [{'error': str(e)}]
        
        return results
    
    def query_dbpedia(self, query: str) -> List[Dict]:
        """Query DBpedia using SPARQL."""
        results = []
        
        try:
            sparql_query = f"""
            PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
            PREFIX dbo: <http://dbpedia.org/ontology/>
            
            SELECT ?entity ?label ?abstract WHERE {{
                ?entity rdfs:label ?label .
                ?entity dbo:abstract ?abstract .
                FILTER (LANG(?label) = "en")
                FILTER (LANG(?abstract) = "en")
                FILTER (CONTAINS(LCASE(STR(?label)), LCASE("{query}")))
            }}
            LIMIT 10
            """
            
            params = {
                'query': sparql_query,
                'format': 'json'
            }
            
            response = self.session.get(self.DBPEDIA_SPARQL, params=params, timeout=10)
            response.raise_for_status()
            
            data = response.json()
            
            for binding in data.get('results', {}).get('bindings', []):
                results.append({
                    'entity': binding['entity']['value'],
                    'label': binding['label']['value'],
                    'abstract': binding['abstract']['value'][:500]
                })
        
        except Exception as e:
            return [{'error': str(e)}]
        
        return results
    
    def link_entities(self, text: str) -> Dict:
        """Link entities in text to knowledge graphs using proper NER."""
        entities = []
        
        # Use NamedEntityRecognizer if available
        if self.ner is not None:
            ner_results = self.ner.extract_entities(text)
            if 'error' not in ner_results:
                # Extract entity texts from relevant categories
                for label in ['PERSON', 'ORG', 'GPE', 'LOC']:
                    if label in ner_results:
                        for ent in ner_results[label]:
                            entities.append(ent['text'])
        else:
            # Fallback: simple entity extraction (capitalized words > 3 chars)
            words = text.split()
            entities = [word for word in words if word[0].isupper() and len(word) > 3]
        
        # Remove duplicates while preserving order
        seen = set()
        unique_entities = []
        for entity in entities:
            if entity not in seen:
                seen.add(entity)
                unique_entities.append(entity)
        
        results = {}
        
        for entity in unique_entities[:5]:  # Limit to top 5 entities
            results[entity] = {
                'wikidata': self.search_wikidata(entity),
                'dbpedia': self.query_dbpedia(entity)
            }
        
        return results

class InteractiveDashboard:
    """Real-time graphs using Plotly."""
    
    def __init__(self):
        if go is None or make_subplots is None:
            raise ImportError("plotly is required for InteractiveDashboard")
        self.data_history = {
            'timestamps': [],
            'response_times': [],
            'status_codes': [],
            'pages_crawled': []
        }
    
    def add_data_point(self, response_time: float, status_code: int, pages_crawled: int):
        """Add a data point to the dashboard."""
        self.data_history['timestamps'].append(datetime.now().strftime('%H:%M:%S'))
        self.data_history['response_times'].append(response_time)
        self.data_history['status_codes'].append(status_code)
        self.data_history['pages_crawled'].append(pages_crawled)
    
    def create_response_time_chart(self) -> str:
        """Create response time chart."""
        fig = go.Figure()
        fig.add_trace(go.Scatter(
            x=self.data_history['timestamps'],
            y=self.data_history['response_times'],
            mode='lines+markers',
            name='Response Time',
            line=dict(color='blue')
        ))
        
        fig.update_layout(
            title='Response Times Over Time',
            xaxis_title='Time',
            yaxis_title='Response Time (s)',
            hovermode='x unified'
        )
        
        return fig.to_html()
    
    def create_status_code_chart(self) -> str:
        """Create status code distribution chart."""
        from collections import Counter
        
        status_counts = Counter(self.data_history['status_codes'])
        
        fig = go.Figure(data=[go.Pie(
            labels=list(status_counts.keys()),
            values=list(status_counts.values()),
            hole=0.3
        )])
        
        fig.update_layout(
            title='Status Code Distribution',
            annotations=[dict(text='Status Codes', x=0.5, y=0.5, font_size=20, showarrow=False)]
        )
        
        return fig.to_html()
    
    def create_pages_crawled_chart(self) -> str:
        """Create cumulative pages crawled chart."""
        fig = go.Figure()
        fig.add_trace(go.Scatter(
            x=self.data_history['timestamps'],
            y=self.data_history['pages_crawled'],
            mode='lines+markers',
            name='Pages Crawled',
            fill='tozeroy',
            line=dict(color='green')
        ))
        
        fig.update_layout(
            title='Cumulative Pages Crawled',
            xaxis_title='Time',
            yaxis_title='Total Pages'
        )
        
        return fig.to_html()
    
    def create_dashboard(self) -> str:
        """Create complete dashboard with all charts."""
        dashboard_html = """
        <!DOCTYPE html>
        <html>
        <head>
            <title>Recon Tool Dashboard</title>
            <script src="https://cdn.plot.ly/plotly-latest.min.js"></script>
            <style>
                body { font-family: Arial, sans-serif; margin: 20px; }
                .chart-container { margin: 20px 0; }
                h1 { color: #333; }
            </style>
        </head>
        <body>
            <h1>Recon Tool Real-Time Dashboard</h1>
            <div class="chart-container" id="response-time-chart"></div>
            <div class="chart-container" id="status-code-chart"></div>
            <div class="chart-container" id="pages-crawled-chart"></div>
            <script>
        """
        
        dashboard_html += self.create_response_time_chart()
        dashboard_html += self.create_status_code_chart()
        dashboard_html += self.create_pages_crawled_chart()
        
        dashboard_html += """
            </script>
        </body>
        </html>
        """
        
        return dashboard_html
    
    def save_dashboard(self, output_path: str = "dashboard.html"):
        """Save dashboard to HTML file."""
        dashboard_html = self.create_dashboard()
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(dashboard_html)
        return output_path
    
    def clear_data(self):
        """Clear all historical data."""
        self.data_history = {
            'timestamps': [],
            'response_times': [],
            'status_codes': [],
            'pages_crawled': []
        }

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
        
        # Advanced feature instances
        try:
            self.network_graph = NetworkGraphGenerator()
        except:
            self.network_graph = None
        
        try:
            self.content_classifier = ContentClassifier()
        except:
            self.content_classifier = None
        
        try:
            self.ner = NamedEntityRecognizer()
        except:
            self.ner = None
        
        self.contact_harvester = ContactHarvester()
        self.tech_fingerprinter = TechnologyStackFingerprinter()
        
        try:
            self.visual_analyzer = VisualAnalyzer()
        except:
            self.visual_analyzer = None
        
        try:
            self.ocr_engine = OCREngine()
        except:
            self.ocr_engine = None
        
        self.temporal_analyzer = TemporalAnalyzer()
        self.statistical_analyzer = StatisticalAnalyzer()
        
        try:
            self.dashboard = InteractiveDashboard()
        except:
            self.dashboard = None
        
        # New OSINT feature instances
        self.ip_geolocation = IPGeolocation()
        self.ssl_tls_analyzer = SSLTLSAnalyzer()
        self.traceroute_analyzer = TracerouteAnalyzer()
        self.vulnerability_scanner = VulnerabilityScanner()
        self.social_media_searcher = SocialMediaSearcher()
        self.backlink_discovery = BacklinkDiscovery()
        self.passive_osint = PassiveOSINT()
        self.knowledge_graph_linker = KnowledgeGraphLinker()
        
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
        self.create_network_graph_tab()
        self.create_content_analysis_tab()
        self.create_contact_harvest_tab()
        self.create_tech_fingerprint_tab()
        self.create_visual_analysis_tab()
        self.create_temporal_analysis_tab()
        self.create_statistics_tab()
        self.create_dashboard_tab()
        self.create_ip_geolocation_tab()
        self.create_ssl_tls_tab()
        self.create_traceroute_tab()
        self.create_vulnerability_scan_tab()
        self.create_social_media_tab()
        self.create_backlink_tab()
        self.create_passive_osint_tab()
        self.create_knowledge_graph_tab()
        
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
        self.num_results.setRange(1, 1000)
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
        
        self.rate_limit_delay = QDoubleSpinBox()
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
    
    def create_network_graph_tab(self):
        """Create tab for network graph visualization."""
        graph_tab = QWidget()
        layout = QVBoxLayout(graph_tab)
        
        # Graph controls
        control_group = QGroupBox("Graph Controls")
        control_layout = QHBoxLayout()
        
        generate_btn = QPushButton("Generate Graph from Crawl Results")
        generate_btn.clicked.connect(self.generate_network_graph)
        control_layout.addWidget(generate_btn)
        
        export_btn = QPushButton("Export Graph")
        export_btn.clicked.connect(self.export_network_graph)
        control_layout.addWidget(export_btn)
        
        control_group.setLayout(control_layout)
        layout.addWidget(control_group)
        
        # Graph display area
        self.graph_display = QTextEdit()
        self.graph_display.setReadOnly(True)
        self.graph_display.setPlaceholderText("Network graph will be displayed here...")
        layout.addWidget(self.graph_display)
        
        # Metrics display
        self.graph_metrics = QTextEdit()
        self.graph_metrics.setReadOnly(True)
        self.graph_metrics.setMaximumHeight(150)
        self.graph_metrics.setPlaceholderText("Graph metrics will appear here...")
        layout.addWidget(self.graph_metrics)
        
        self.tab_widget.addTab(graph_tab, "Network Graph")
    
    def create_content_analysis_tab(self):
        """Create tab for content classification and NER."""
        analysis_tab = QWidget()
        layout = QVBoxLayout(analysis_tab)
        
        # Content classification group
        class_group = QGroupBox("Content Classification")
        class_layout = QFormLayout()
        
        self.classify_text = QTextEdit()
        self.classify_text.setMaximumHeight(100)
        self.classify_text.setPlaceholderText("Enter text to classify...")
        class_layout.addRow("Text:", self.classify_text)
        
        self.classify_type = QComboBox()
        self.classify_type.addItems(['Sentiment', 'Topic'])
        class_layout.addRow("Type:", self.classify_type)
        
        self.topic_labels = QLineEdit()
        self.topic_labels.setPlaceholderText("Comma-separated topics (for topic classification)")
        class_layout.addRow("Topics:", self.topic_labels)
        
        classify_btn = QPushButton("Classify")
        classify_btn.clicked.connect(self.perform_classification)
        class_layout.addRow("", classify_btn)
        
        class_group.setLayout(class_layout)
        layout.addWidget(class_group)
        
        # NER group
        ner_group = QGroupBox("Named Entity Recognition")
        ner_layout = QFormLayout()
        
        self.ner_text = QTextEdit()
        self.ner_text.setMaximumHeight(100)
        self.ner_text.setPlaceholderText("Enter text for NER...")
        ner_layout.addRow("Text:", self.ner_text)
        
        ner_btn = QPushButton("Extract Entities")
        ner_btn.clicked.connect(self.perform_ner)
        ner_layout.addRow("", ner_btn)
        
        ner_group.setLayout(ner_layout)
        layout.addWidget(ner_group)
        
        # Results display
        self.analysis_results = QTextEdit()
        self.analysis_results.setReadOnly(True)
        layout.addWidget(self.analysis_results)
        
        self.tab_widget.addTab(analysis_tab, "Content Analysis")
    
    def create_contact_harvest_tab(self):
        """Create tab for contact harvesting."""
        contact_tab = QWidget()
        layout = QVBoxLayout(contact_tab)
        
        # Contact extraction group
        extract_group = QGroupBox("Contact Extraction")
        extract_layout = QFormLayout()
        
        self.contact_text = QTextEdit()
        self.contact_text.setMaximumHeight(100)
        self.contact_text.setPlaceholderText("Enter text or HTML to extract contacts...")
        extract_layout.addRow("Text/HTML:", self.contact_text)
        
        self.contact_types = QCheckBox("Extract All Types")
        self.contact_types.setChecked(True)
        extract_layout.addRow("", self.contact_types)
        
        extract_btn = QPushButton("Extract Contacts")
        extract_btn.clicked.connect(self.perform_contact_extraction)
        extract_layout.addRow("", extract_btn)
        
        extract_group.setLayout(extract_layout)
        layout.addWidget(extract_group)
        
        # Results display
        self.contact_results = QTextEdit()
        self.contact_results.setReadOnly(True)
        layout.addWidget(self.contact_results)
        
        self.tab_widget.addTab(contact_tab, "Contact Harvest")
    
    def create_tech_fingerprint_tab(self):
        """Create tab for technology stack fingerprinting."""
        tech_tab = QWidget()
        layout = QVBoxLayout(tech_tab)
        
        # Fingerprint controls
        fp_group = QGroupBox("Technology Fingerprinting")
        fp_layout = QFormLayout()
        
        self.fp_url = QLineEdit()
        self.fp_url.setPlaceholderText("Enter URL to fingerprint...")
        fp_layout.addRow("URL:", self.fp_url)
        
        self.fp_html = QTextEdit()
        self.fp_html.setMaximumHeight(150)
        self.fp_html.setPlaceholderText("Paste HTML content here (or leave blank to fetch)...")
        fp_layout.addRow("HTML:", self.fp_html)
        
        fingerprint_btn = QPushButton("Fingerprint Technology Stack")
        fingerprint_btn.clicked.connect(self.perform_tech_fingerprint)
        fp_layout.addRow("", fingerprint_btn)
        
        fp_group.setLayout(fp_layout)
        layout.addWidget(fp_group)
        
        # Results display
        self.fp_results = QTextEdit()
        self.fp_results.setReadOnly(True)
        layout.addWidget(self.fp_results)
        
        self.tab_widget.addTab(tech_tab, "Tech Fingerprint")
    
    def create_visual_analysis_tab(self):
        """Create tab for visual analysis and OCR."""
        visual_tab = QWidget()
        layout = QVBoxLayout(visual_tab)
        
        # Screenshot group
        screenshot_group = QGroupBox("Screenshot & Visual Analysis")
        screenshot_layout = QFormLayout()
        
        self.screenshot_url = QLineEdit()
        self.screenshot_url.setPlaceholderText("Enter URL to screenshot...")
        screenshot_layout.addRow("URL:", self.screenshot_url)
        
        screenshot_btn = QPushButton("Capture Screenshot")
        screenshot_btn.clicked.connect(self.capture_screenshot)
        screenshot_layout.addRow("", screenshot_btn)
        
        screenshot_group.setLayout(screenshot_layout)
        layout.addWidget(screenshot_group)
        
        # OCR group
        ocr_group = QGroupBox("OCR Text Extraction")
        ocr_layout = QFormLayout()
        
        self.ocr_image_path = QLineEdit()
        self.ocr_image_path.setPlaceholderText("Enter image path or URL...")
        ocr_layout.addRow("Image:", self.ocr_image_path)
        
        ocr_btn = QPushButton("Extract Text")
        ocr_btn.clicked.connect(self.perform_ocr)
        ocr_layout.addRow("", ocr_btn)
        
        ocr_group.setLayout(ocr_layout)
        layout.addWidget(ocr_group)
        
        # Results display
        self.visual_results = QTextEdit()
        self.visual_results.setReadOnly(True)
        layout.addWidget(self.visual_results)
        
        self.tab_widget.addTab(visual_tab, "Visual Analysis")
    
    def create_temporal_analysis_tab(self):
        """Create tab for temporal analysis and change detection."""
        temporal_tab = QWidget()
        layout = QVBoxLayout(temporal_tab)
        
        # Baseline capture
        baseline_group = QGroupBox("Baseline Capture")
        baseline_layout = QFormLayout()
        
        self.baseline_url = QLineEdit()
        self.baseline_url.setPlaceholderText("Enter URL to baseline...")
        baseline_layout.addRow("URL:", self.baseline_url)
        
        self.baseline_content = QTextEdit()
        self.baseline_content.setMaximumHeight(100)
        self.baseline_content.setPlaceholderText("Enter content to baseline...")
        baseline_layout.addRow("Content:", self.baseline_content)
        
        capture_baseline_btn = QPushButton("Capture Baseline")
        capture_baseline_btn.clicked.connect(self.capture_baseline)
        baseline_layout.addRow("", capture_baseline_btn)
        
        baseline_group.setLayout(baseline_layout)
        layout.addWidget(baseline_group)
        
        # Change detection
        change_group = QGroupBox("Change Detection")
        change_layout = QFormLayout()
        
        self.current_content = QTextEdit()
        self.current_content.setMaximumHeight(100)
        self.current_content.setPlaceholderText("Enter current content...")
        change_layout.addRow("Current Content:", self.current_content)
        
        self.alert_patterns = QLineEdit()
        self.alert_patterns.setPlaceholderText("Alert patterns (comma-separated regex)...")
        change_layout.addRow("Alert Patterns:", self.alert_patterns)
        
        detect_changes_btn = QPushButton("Detect Changes")
        detect_changes_btn.clicked.connect(self.detect_changes)
        change_layout.addRow("", detect_changes_btn)
        
        change_group.setLayout(change_layout)
        layout.addWidget(change_group)
        
        # Results display
        self.temporal_results = QTextEdit()
        self.temporal_results.setReadOnly(True)
        layout.addWidget(self.temporal_results)
        
        self.tab_widget.addTab(temporal_tab, "Temporal Analysis")
    
    def create_statistics_tab(self):
        """Create tab for statistical analysis."""
        stats_tab = QWidget()
        layout = QVBoxLayout(stats_tab)
        
        # Statistics controls
        stats_group = QGroupBox("Statistical Analysis")
        stats_layout = QFormLayout()
        
        generate_stats_btn = QPushButton("Generate Statistics from Crawl Results")
        generate_stats_btn.clicked.connect(self.generate_statistics)
        stats_layout.addRow("", generate_stats_btn)
        
        stats_group.setLayout(stats_layout)
        layout.addWidget(stats_group)
        
        # Results display
        self.stats_results = QTextEdit()
        self.stats_results.setReadOnly(True)
        layout.addWidget(self.stats_results)
        
        self.tab_widget.addTab(stats_tab, "Statistics")
    
    def create_dashboard_tab(self):
        """Create tab for interactive dashboard."""
        dashboard_tab = QWidget()
        layout = QVBoxLayout(dashboard_tab)
        
        # Dashboard controls
        dash_group = QGroupBox("Dashboard Controls")
        dash_layout = QHBoxLayout()
        
        refresh_btn = QPushButton("Refresh Dashboard")
        refresh_btn.clicked.connect(self.refresh_dashboard)
        dash_layout.addWidget(refresh_btn)
        
        save_btn = QPushButton("Save Dashboard")
        save_btn.clicked.connect(self.save_dashboard)
        dash_layout.addWidget(save_btn)
        
        dash_group.setLayout(dash_layout)
        layout.addWidget(dash_group)
        
        # Dashboard display (using web view if available)
        if QWebEngineView is not None:
            self.dashboard_view = QWebEngineView()
            layout.addWidget(self.dashboard_view)
        else:
            self.dashboard_display = QTextEdit()
            self.dashboard_display.setReadOnly(True)
            self.dashboard_display.setPlaceholderText("Dashboard HTML will be displayed here...")
            layout.addWidget(self.dashboard_display)
        
        self.tab_widget.addTab(dashboard_tab, "Dashboard")
    
    def create_ip_geolocation_tab(self):
        """Create tab for IP geolocation and ASN mapping."""
        geo_tab = QWidget()
        layout = QVBoxLayout(geo_tab)
        
        # Geolocation controls
        geo_group = QGroupBox("IP Geolocation")
        geo_layout = QFormLayout()
        
        self.geo_ip = QLineEdit()
        self.geo_ip.setPlaceholderText("Enter IP address...")
        geo_layout.addRow("IP Address:", self.geo_ip)
        
        geolocate_btn = QPushButton("Geolocate IP")
        geolocate_btn.clicked.connect(self.perform_geolocation)
        geo_layout.addRow("", geolocate_btn)
        
        generate_map_btn = QPushButton("Generate Map")
        generate_map_btn.clicked.connect(self.generate_geo_map)
        geo_layout.addRow("", generate_map_btn)
        
        geo_group.setLayout(geo_layout)
        layout.addWidget(geo_group)
        
        # Results display
        self.geo_results = QTextEdit()
        self.geo_results.setReadOnly(True)
        layout.addWidget(self.geo_results)
        
        self.tab_widget.addTab(geo_tab, "IP Geolocation")
    
    def create_ssl_tls_tab(self):
        """Create tab for SSL/TLS analysis."""
        ssl_tab = QWidget()
        layout = QVBoxLayout(ssl_tab)
        
        # SSL/TLS controls
        ssl_group = QGroupBox("SSL/TLS Analysis")
        ssl_layout = QFormLayout()
        
        self.ssl_url = QLineEdit()
        self.ssl_url.setPlaceholderText("Enter URL (e.g., https://example.com)")
        ssl_layout.addRow("URL:", self.ssl_url)
        
        analyze_cert_btn = QPushButton("Analyze Certificate")
        analyze_cert_btn.clicked.connect(self.analyze_ssl_certificate)
        ssl_layout.addRow("", analyze_cert_btn)
        
        check_headers_btn = QPushButton("Check Security Headers")
        check_headers_btn.clicked.connect(self.check_ssl_headers)
        ssl_layout.addRow("", check_headers_btn)
        
        full_analysis_btn = QPushButton("Full Analysis")
        full_analysis_btn.clicked.connect(self.full_ssl_analysis)
        ssl_layout.addRow("", full_analysis_btn)
        
        ssl_group.setLayout(ssl_layout)
        layout.addWidget(ssl_group)
        
        # Results display
        self.ssl_results = QTextEdit()
        self.ssl_results.setReadOnly(True)
        layout.addWidget(self.ssl_results)
        
        self.tab_widget.addTab(ssl_tab, "SSL/TLS")
    
    def create_traceroute_tab(self):
        """Create tab for traceroute and latency analysis."""
        trace_tab = QWidget()
        layout = QVBoxLayout(trace_tab)
        
        # Traceroute controls
        trace_group = QGroupBox("Traceroute & Latency")
        trace_layout = QFormLayout()
        
        self.trace_target = QLineEdit()
        self.trace_target.setPlaceholderText("Enter hostname or IP...")
        trace_layout.addRow("Target:", self.trace_target)
        
        latency_btn = QPushButton("Measure Latency")
        latency_btn.clicked.connect(self.measure_latency)
        trace_layout.addRow("", latency_btn)
        
        traceroute_btn = QPushButton("Traceroute")
        traceroute_btn.clicked.connect(self.perform_traceroute)
        trace_layout.addRow("", traceroute_btn)
        
        multi_region_btn = QPushButton("Multi-Region Latency")
        multi_region_btn.clicked.connect(self.multi_region_latency)
        trace_layout.addRow("", multi_region_btn)
        
        trace_group.setLayout(trace_layout)
        layout.addWidget(trace_group)
        
        # Results display
        self.trace_results = QTextEdit()
        self.trace_results.setReadOnly(True)
        layout.addWidget(self.trace_results)
        
        self.tab_widget.addTab(trace_tab, "Traceroute")
    
    def create_vulnerability_scan_tab(self):
        """Create tab for vulnerability scanning."""
        vuln_tab = QWidget()
        layout = QVBoxLayout(vuln_tab)
        
        # Vulnerability scan controls
        vuln_group = QGroupBox("Vulnerability Scanner")
        vuln_layout = QFormLayout()
        
        self.vuln_url = QLineEdit()
        self.vuln_url.setPlaceholderText("Enter URL to scan...")
        vuln_layout.addRow("URL:", self.vuln_url)
        
        scan_files_btn = QPushButton("Scan Exposed Files")
        scan_files_btn.clicked.connect(self.scan_exposed_files)
        vuln_layout.addRow("", scan_files_btn)
        
        scan_headers_btn = QPushButton("Scan Security Headers")
        scan_headers_btn.clicked.connect(self.scan_security_headers)
        vuln_layout.addRow("", scan_headers_btn)
        
        scan_admin_btn = QPushButton("Scan Admin Panels")
        scan_admin_btn.clicked.connect(self.scan_admin_panels)
        vuln_layout.addRow("", scan_admin_btn)
        
        full_scan_btn = QPushButton("Full Vulnerability Scan")
        full_scan_btn.clicked.connect(self.full_vulnerability_scan)
        vuln_layout.addRow("", full_scan_btn)
        
        vuln_group.setLayout(vuln_layout)
        layout.addWidget(vuln_group)
        
        # Results display
        self.vuln_results = QTextEdit()
        self.vuln_results.setReadOnly(True)
        layout.addWidget(self.vuln_results)
        
        self.tab_widget.addTab(vuln_tab, "Vulnerability Scan")
    
    def create_social_media_tab(self):
        """Create tab for social media search."""
        social_tab = QWidget()
        layout = QVBoxLayout(social_tab)
        
        # Social media controls
        social_group = QGroupBox("Social Media Search")
        social_layout = QFormLayout()
        
        self.social_query = QLineEdit()
        self.social_query.setPlaceholderText("Enter search query...")
        social_layout.addRow("Query:", self.social_query)
        
        # API credentials
        self.reddit_client_id = QLineEdit()
        self.reddit_client_id.setPlaceholderText("Reddit Client ID (optional)")
        social_layout.addRow("Reddit Client ID:", self.reddit_client_id)
        
        self.reddit_client_secret = QLineEdit()
        self.reddit_client_secret.setPlaceholderText("Reddit Client Secret (optional)")
        social_layout.addRow("Reddit Secret:", self.reddit_client_secret)
        
        search_reddit_btn = QPushButton("Search Reddit")
        search_reddit_btn.clicked.connect(self.search_social_media)
        social_layout.addRow("", search_reddit_btn)
        
        social_group.setLayout(social_layout)
        layout.addWidget(social_group)
        
        # Results display
        self.social_results = QTextEdit()
        self.social_results.setReadOnly(True)
        layout.addWidget(self.social_results)
        
        self.tab_widget.addTab(social_tab, "Social Media")
    
    def create_backlink_tab(self):
        """Create tab for backlink discovery."""
        backlink_tab = QWidget()
        layout = QVBoxLayout(backlink_tab)
        
        # Backlink controls
        backlink_group = QGroupBox("Backlink Discovery")
        backlink_layout = QFormLayout()
        
        self.backlink_url = QLineEdit()
        self.backlink_url.setPlaceholderText("Enter target URL...")
        backlink_layout.addRow("URL:", self.backlink_url)
        
        discover_btn = QPushButton("Discover Backlinks")
        discover_btn.clicked.connect(self.discover_backlinks)
        backlink_layout.addRow("", discover_btn)
        
        backlink_group.setLayout(backlink_layout)
        layout.addWidget(backlink_group)
        
        # Results display
        self.backlink_results = QTextEdit()
        self.backlink_results.setReadOnly(True)
        layout.addWidget(self.backlink_results)
        
        self.tab_widget.addTab(backlink_tab, "Backlinks")
    
    def create_passive_osint_tab(self):
        """Create tab for passive OSINT correlation."""
        osint_tab = QWidget()
        layout = QVBoxLayout(osint_tab)
        
        # OSINT controls
        osint_group = QGroupBox("Passive OSINT")
        osint_layout = QFormLayout()
        
        self.osint_target = QLineEdit()
        self.osint_target.setPlaceholderText("Enter IP or domain...")
        osint_layout.addRow("Target:", self.osint_target)
        
        # API credentials
        self.shodan_key = QLineEdit()
        self.shodan_key.setPlaceholderText("Shodan API Key (optional)")
        osint_layout.addRow("Shodan Key:", self.shodan_key)
        
        self.virustotal_key = QLineEdit()
        self.virustotal_key.setPlaceholderText("VirusTotal API Key (optional)")
        osint_layout.addRow("VirusTotal Key:", self.virustotal_key)
        
        self.abuseipdb_key = QLineEdit()
        self.abuseipdb_key.setPlaceholderText("AbuseIPDB API Key (optional)")
        osint_layout.addRow("AbuseIPDB Key:", self.abuseipdb_key)
        
        correlate_btn = QPushButton("Correlate OSINT")
        correlate_btn.clicked.connect(self.correlate_osint)
        osint_layout.addRow("", correlate_btn)
        
        osint_group.setLayout(osint_layout)
        layout.addWidget(osint_group)
        
        # Results display
        self.osint_results = QTextEdit()
        self.osint_results.setReadOnly(True)
        layout.addWidget(self.osint_results)
        
        self.tab_widget.addTab(osint_tab, "Passive OSINT")
    
    def create_knowledge_graph_tab(self):
        """Create tab for knowledge graph linking."""
        kg_tab = QWidget()
        layout = QVBoxLayout(kg_tab)
        
        # Knowledge graph controls
        kg_group = QGroupBox("Knowledge Graph Linking")
        kg_layout = QFormLayout()
        
        self.kg_text = QTextEdit()
        self.kg_text.setMaximumHeight(100)
        self.kg_text.setPlaceholderText("Enter text to extract entities...")
        kg_layout.addRow("Text:", self.kg_text)
        
        link_btn = QPushButton("Link Entities")
        link_btn.clicked.connect(self.link_knowledge_graph)
        kg_layout.addRow("", link_btn)
        
        kg_group.setLayout(kg_layout)
        layout.addWidget(kg_group)
        
        # Results display
        self.kg_results = QTextEdit()
        self.kg_results.setReadOnly(True)
        layout.addWidget(self.kg_results)
        
        self.tab_widget.addTab(kg_tab, "Knowledge Graph")
    
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
    
    # Network Graph handlers
    def generate_network_graph(self):
        if self.network_graph is None:
            QMessageBox.warning(self, "Warning", "Network graph feature not available. Install networkx and matplotlib.")
            return
        
        if not self.current_results:
            QMessageBox.warning(self, "Warning", "No crawl results to generate graph from")
            return
        
        try:
            self.network_graph = NetworkGraphGenerator()
            self.network_graph.build_from_crawl_results(self.current_results)
            
            metrics = self.network_graph.calculate_metrics()
            metrics_text = "Graph Metrics:\n"
            for key, value in metrics.items():
                if isinstance(value, dict):
                    metrics_text += f"{key}: {len(value)} entries\n"
                else:
                    metrics_text += f"{key}: {value}\n"
            
            self.graph_metrics.setText(metrics_text)
            self.graph_display.setText(f"Graph generated with {metrics.get('num_nodes', 0)} nodes and {metrics.get('num_edges', 0)} edges")
            
            self.status_label.setText("Network graph generated successfully")
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Failed to generate graph: {str(e)}")
    
    def export_network_graph(self):
        if self.network_graph is None:
            QMessageBox.warning(self, "Warning", "Network graph feature not available")
            return
        
        filename, _ = QFileDialog.getSaveFileName(
            self, "Export Network Graph", 
            "network_graph.png", 
            "PNG files (*.png);;GEXF files (*.gexf);;GraphML files (*.graphml)"
        )
        
        if filename:
            try:
                if filename.endswith('.png'):
                    self.network_graph.visualize(filename)
                elif filename.endswith('.gexf'):
                    self.network_graph.export_graph(filename, 'gexf')
                elif filename.endswith('.graphml'):
                    self.network_graph.export_graph(filename, 'graphml')
                
                QMessageBox.information(self, "Success", f"Graph exported to {filename}")
            except Exception as e:
                QMessageBox.critical(self, "Error", f"Failed to export graph: {str(e)}")
    
    # Content Analysis handlers
    def perform_classification(self):
        if self.content_classifier is None:
            QMessageBox.warning(self, "Warning", "Content classification not available. Install transformers library.")
            return
        
        text = self.classify_text.toPlainText().strip()
        if not text:
            QMessageBox.warning(self, "Warning", "Please enter text to classify")
            return
        
        classify_type = self.classify_type.currentText().lower()
        
        try:
            if classify_type == 'sentiment':
                result = self.content_classifier.classify_sentiment(text)
                output = f"Sentiment Analysis:\n"
                output += f"Label: {result.get('label', 'N/A')}\n"
                output += f"Score: {result.get('score', 'N/A'):.4f}\n"
            elif classify_type == 'topic':
                topics = [t.strip() for t in self.topic_labels.text().split(',') if t.strip()]
                if not topics:
                    QMessageBox.warning(self, "Warning", "Please enter topic labels")
                    return
                
                result = self.content_classifier.classify_topic(text, topics)
                output = f"Topic Classification:\n"
                output += f"Top Topic: {result.get('top_topic', 'N/A')}\n"
                output += f"Confidence: {result.get('confidence', 'N/A'):.4f}\n"
                output += "\nAll Topics:\n"
                for topic, score in result.get('all_topics', []):
                    output += f"  {topic}: {score:.4f}\n"
            
            self.analysis_results.setText(output)
            self.status_label.setText("Classification complete")
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Classification failed: {str(e)}")
    
    def perform_ner(self):
        if self.ner is None:
            QMessageBox.warning(self, "Warning", "NER not available. Install spaCy and download model.")
            return
        
        text = self.ner_text.toPlainText().strip()
        if not text:
            QMessageBox.warning(self, "Warning", "Please enter text for NER")
            return
        
        try:
            entities = self.ner.extract_entities(text)
            
            output = "Named Entities:\n\n"
            for entity_type, entity_list in entities.items():
                if entity_list:
                    output += f"{entity_type}:\n"
                    for entity in entity_list:
                        output += f"  - {entity['text']} (position {entity['start']}-{entity['end']})\n"
                    output += "\n"
            
            if not any(entities.values()):
                output = "No entities found."
            
            self.analysis_results.setText(output)
            self.status_label.setText("NER complete")
        except Exception as e:
            QMessageBox.critical(self, "Error", f"NER failed: {str(e)}")
    
    # Contact Harvest handlers
    def perform_contact_extraction(self):
        text = self.contact_text.toPlainText().strip()
        if not text:
            QMessageBox.warning(self, "Warning", "Please enter text or HTML")
            return
        
        try:
            # Check if it's HTML
            if '<html' in text.lower() or '<body' in text.lower():
                results = self.contact_harvester.extract_from_html(text)
            else:
                results = self.contact_harvester.extract_contacts(text)
            
            output = "Extracted Contacts:\n\n"
            for contact_type, contacts in results.items():
                if contacts:
                    output += f"{contact_type.title()}:\n"
                    for contact in contacts:
                        output += f"  - {contact}\n"
                    output += "\n"
            
            if not any(results.values()):
                output = "No contacts found."
            
            self.contact_results.setText(output)
            self.status_label.setText("Contact extraction complete")
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Contact extraction failed: {str(e)}")
    
    # Tech Fingerprint handlers
    def perform_tech_fingerprint(self):
        url = self.fp_url.text().strip()
        if not url:
            QMessageBox.warning(self, "Warning", "Please enter a URL")
            return
        
        html = self.fp_html.toPlainText().strip()
        
        try:
            if not html:
                # Fetch HTML
                response = requests.get(url, timeout=10)
                html = response.text
                headers = dict(response.headers)
            else:
                headers = {}
            
            results = self.tech_fingerprinter.fingerprint(url, html, headers)
            report = self.tech_fingerprinter.generate_report()
            
            self.fp_results.setText(report)
            self.status_label.setText("Technology fingerprinting complete")
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Fingerprinting failed: {str(e)}")
    
    # Visual Analysis handlers
    def capture_screenshot(self):
        if self.visual_analyzer is None:
            QMessageBox.warning(self, "Warning", "Visual analysis not available. Install PIL and imagehash.")
            return
        
        url = self.screenshot_url.text().strip()
        if not url:
            QMessageBox.warning(self, "Warning", "Please enter a URL")
            return
        
        try:
            screenshot_path = self.visual_analyzer.capture_screenshot(url)
            if screenshot_path:
                self.visual_results.setText(f"Screenshot saved to: {screenshot_path}")
                self.status_label.setText("Screenshot captured")
            else:
                self.visual_results.setText("Failed to capture screenshot")
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Screenshot failed: {str(e)}")
    
    def perform_ocr(self):
        if self.ocr_engine is None:
            QMessageBox.warning(self, "Warning", "OCR not available. Install pytesseract and Tesseract.")
            return
        
        image_path = self.ocr_image_path.text().strip()
        if not image_path:
            QMessageBox.warning(self, "Warning", "Please enter image path or URL")
            return
        
        try:
            if image_path.startswith('http'):
                text = self.ocr_engine.extract_from_url(image_path)
            else:
                text = self.ocr_engine.extract_text(image_path)
            
            self.visual_results.setText(f"Extracted Text:\n\n{text}")
            self.status_label.setText("OCR complete")
        except Exception as e:
            QMessageBox.critical(self, "Error", f"OCR failed: {str(e)}")
    
    # Temporal Analysis handlers
    def capture_baseline(self):
        url = self.baseline_url.text().strip()
        content = self.baseline_content.toPlainText().strip()
        
        if not url or not content:
            QMessageBox.warning(self, "Warning", "Please enter URL and content")
            return
        
        try:
            baseline = self.temporal_analyzer.capture_baseline(url, content)
            self.temporal_results.setText(f"Baseline captured at {baseline['timestamp']}")
            self.status_label.setText("Baseline captured")
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Baseline capture failed: {str(e)}")
    
    def detect_changes(self):
        url = self.baseline_url.text().strip()
        current_content = self.current_content.toPlainText().strip()
        
        if not current_content:
            QMessageBox.warning(self, "Warning", "Please enter current content")
            return
        
        alert_patterns = None
        if self.alert_patterns.text().strip():
            alert_patterns = [p.strip() for p in self.alert_patterns.text().split(',')]
        
        try:
            changes = self.temporal_analyzer.detect_changes(url, current_content, alert_patterns)
            
            output = "Change Detection Results:\n\n"
            output += f"Content Changed: {changes.get('content_changed', False)}\n"
            output += f"Baseline Timestamp: {changes.get('baseline_timestamp', 'N/A')}\n"
            output += f"Current Timestamp: {changes.get('timestamp', 'N/A')}\n\n"
            
            if changes.get('content_changed'):
                output += f"Diff:\n{changes.get('text_diff', {}).get('diff', 'N/A')}\n\n"
                
                if changes.get('pattern_matches'):
                    output += "Pattern Matches:\n"
                    for match in changes['pattern_matches']:
                        output += f"  - Pattern: {match['pattern']}\n"
                        output += f"    Match: {match['match']}\n"
                        output += f"    Position: {match['position']}\n\n"
            
            self.temporal_results.setText(output)
            self.status_label.setText("Change detection complete")
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Change detection failed: {str(e)}")
    
    # Statistics handlers
    def generate_statistics(self):
        if not self.current_results:
            QMessageBox.warning(self, "Warning", "No crawl results to analyze")
            return
        
        try:
            # Extract real metrics from crawl results
            for result in self.current_results:
                self.statistical_analyzer.record_metric(
                    url=result.get('url', ''),
                    response_time=result.get('response_time', 0),
                    status_code=result.get('status_code', 0),
                    content_type=result.get('content_type', 'text/html'),
                    page_size=result.get('page_size', 0),
                    outbound_links=result.get('links', [])
                )
            
            report = self.statistical_analyzer.generate_report()
            self.stats_results.setText(report)
            self.status_label.setText("Statistics generated")
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Statistics generation failed: {str(e)}")
    
    # Dashboard handlers
    def refresh_dashboard(self):
        if self.dashboard is None:
            QMessageBox.warning(self, "Warning", "Dashboard not available. Install plotly.")
            return
        
        try:
            # Add some sample data
            for i in range(10):
                self.dashboard.add_data_point(
                    response_time=0.3 + (i * 0.1),
                    status_code=200,
                    pages_crawled=(i + 1) * 5
                )
            
            dashboard_html = self.dashboard.create_dashboard()
            
            if QWebEngineView is not None:
                self.dashboard_view.setHtml(dashboard_html)
            else:
                self.dashboard_display.setText(dashboard_html)
            
            self.status_label.setText("Dashboard refreshed")
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Dashboard refresh failed: {str(e)}")
    
    def save_dashboard(self):
        if self.dashboard is None:
            QMessageBox.warning(self, "Warning", "Dashboard not available")
            return
        
        filename, _ = QFileDialog.getSaveFileName(
            self, "Save Dashboard", 
            "dashboard.html", 
            "HTML files (*.html)"
        )
        
        if filename:
            try:
                self.dashboard.save_dashboard(filename)
                QMessageBox.information(self, "Success", f"Dashboard saved to {filename}")
            except Exception as e:
                QMessageBox.critical(self, "Error", f"Failed to save dashboard: {str(e)}")
    
    # New OSINT feature handlers
    def perform_geolocation(self):
        ip = self.geo_ip.text().strip()
        if not ip:
            QMessageBox.warning(self, "Warning", "Please enter an IP address")
            return
        
        try:
            result = self.ip_geolocation.geolocate_ip(ip)
            
            output = f"IP Geolocation Results:\n\n"
            output += f"IP: {result['ip']}\n"
            output += f"Country: {result.get('country', 'N/A')}\n"
            output += f"City: {result.get('city', 'N/A')}\n"
            output += f"Latitude: {result.get('latitude', 'N/A')}\n"
            output += f"Longitude: {result.get('longitude', 'N/A')}\n"
            output += f"ASN: {result.get('asn', 'N/A')}\n"
            output += f"Organization: {result.get('org', 'N/A')}\n"
            
            if result.get('error'):
                output += f"Error: {result['error']}\n"
            
            self.geo_results.setText(output)
            self.status_label.setText(f"Geolocation complete for {ip}")
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Geolocation failed: {str(e)}")
    
    def generate_geo_map(self):
        ip = self.geo_ip.text().strip()
        if not ip:
            QMessageBox.warning(self, "Warning", "Please enter an IP address first")
            return
        
        try:
            result = self.ip_geolocation.geolocate_ip(ip)
            if result.get('latitude') and result.get('longitude'):
                map_path = self.ip_geolocation.generate_map([result])
                if map_path:
                    QMessageBox.information(self, "Success", f"Map generated: {map_path}")
                    self.geo_results.setText(f"Map saved to: {map_path}")
                else:
                    QMessageBox.warning(self, "Warning", "Failed to generate map (folium not available)")
            else:
                QMessageBox.warning(self, "Warning", "No coordinates available for this IP")
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Map generation failed: {str(e)}")
    
    def analyze_ssl_certificate(self):
        url = self.ssl_url.text().strip()
        if not url:
            QMessageBox.warning(self, "Warning", "Please enter a URL")
            return
        
        try:
            from urllib.parse import urlparse
            hostname = urlparse(url).netloc.split(':')[0]
            
            result = self.ssl_tls_analyzer.analyze_certificate(hostname)
            
            output = f"SSL/TLS Certificate Analysis:\n\n"
            output += f"Hostname: {result['hostname']}\n"
            output += f"Port: {result['port']}\n"
            output += f"Version: {result.get('version', 'N/A')}\n"
            output += f"Cipher: {result.get('cipher', 'N/A')}\n"
            output += f"Weak Cipher: {result.get('weak_cipher', 'N/A')}\n"
            output += f"Issuer: {result.get('issuer', 'N/A')}\n"
            output += f"Subject: {result.get('subject', 'N/A')}\n"
            output += f"Valid From: {result.get('not_before', 'N/A')}\n"
            output += f"Valid Until: {result.get('not_after', 'N/A')}\n"
            output += f"Days Until Expiry: {result.get('days_until_expiry', 'N/A')}\n"
            output += f"Is Valid: {result.get('is_valid', 'N/A')}\n"
            
            if result.get('error'):
                output += f"Error: {result['error']}\n"
            
            self.ssl_results.setText(output)
            self.status_label.setText(f"SSL analysis complete for {hostname}")
        except Exception as e:
            QMessageBox.critical(self, "Error", f"SSL analysis failed: {str(e)}")
    
    def check_ssl_headers(self):
        url = self.ssl_url.text().strip()
        if not url:
            QMessageBox.warning(self, "Warning", "Please enter a URL")
            return
        
        try:
            result = self.ssl_tls_analyzer.check_security_headers(url)
            
            output = f"Security Headers Analysis:\n\n"
            output += f"URL: {result['url']}\n\n"
            
            output += "Present Headers:\n"
            for header, value in result['security_headers'].items():
                if value:
                    output += f"  {header}: {value}\n"
            
            output += "\nMissing Headers:\n"
            for header in result['missing_headers']:
                output += f"  {header}\n"
            
            output += f"\nSecurity Score: {result.get('security_score', 0):.1f}%\n"
            
            if result.get('error'):
                output += f"Error: {result['error']}\n"
            
            self.ssl_results.setText(output)
            self.status_label.setText(f"Security headers check complete for {url}")
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Security headers check failed: {str(e)}")
    
    def full_ssl_analysis(self):
        url = self.ssl_url.text().strip()
        if not url:
            QMessageBox.warning(self, "Warning", "Please enter a URL")
            return
        
        try:
            result = self.ssl_tls_analyzer.full_analysis(url)
            
            output = "Full SSL/TLS Analysis:\n\n"
            
            # Certificate analysis
            cert = result['certificate']
            output += "=== Certificate ===\n"
            output += f"Hostname: {cert['hostname']}\n"
            output += f"Version: {cert.get('version', 'N/A')}\n"
            output += f"Valid: {cert.get('is_valid', 'N/A')}\n"
            output += f"Days until expiry: {cert.get('days_until_expiry', 'N/A')}\n"
            output += f"Weak cipher: {cert.get('weak_cipher', 'N/A')}\n\n"
            
            # Security headers
            headers = result['security_headers']
            output += "=== Security Headers ===\n"
            output += f"Missing: {', '.join(headers['missing_headers'])}\n"
            output += f"Security Score: {headers.get('security_score', 0):.1f}%\n"
            
            self.ssl_results.setText(output)
            self.status_label.setText(f"Full SSL analysis complete for {url}")
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Full SSL analysis failed: {str(e)}")
    
    def measure_latency(self):
        target = self.trace_target.text().strip()
        if not target:
            QMessageBox.warning(self, "Warning", "Please enter a target")
            return
        
        try:
            result = self.traceroute_analyzer.measure_latency(target)
            
            if 'error' in result:
                self.trace_results.setText(f"Error: {result['error']}")
            else:
                output = f"Latency Measurement for {target}:\n\n"
                lat = result['latency_ms']
                output += f"Min: {lat['min']:.2f} ms\n"
                output += f"Max: {lat['max']:.2f} ms\n"
                output += f"Average: {lat['avg']:.2f} ms\n"
                output += f"Median: {lat['median']:.2f} ms\n"
                output += f"Packet Loss: {result['packet_loss']:.1f}%\n"
                
                self.trace_results.setText(output)
            
            self.status_label.setText(f"Latency measurement complete for {target}")
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Latency measurement failed: {str(e)}")
    
    def perform_traceroute(self):
        target = self.trace_target.text().strip()
        if not target:
            QMessageBox.warning(self, "Warning", "Please enter a target")
            return
        
        try:
            results = self.traceroute_analyzer.traceroute(target)
            
            output = f"Traceroute to {target}:\n\n"
            for hop in results:
                if 'error' in hop:
                    output += f"Error: {hop['error']}\n"
                else:
                    output += f"Hop {hop['hop']}: {hop['ip']} - {hop.get('rtt_ms', 'N/A')} ms ({hop['status']})\n"
            
            self.trace_results.setText(output)
            self.status_label.setText(f"Traceroute complete for {target}")
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Traceroute failed: {str(e)}")
    
    def multi_region_latency(self):
        target = self.trace_target.text().strip()
        if not target:
            QMessageBox.warning(self, "Warning", "Please enter a target")
            return
        
        try:
            results = self.traceroute_analyzer.multi_region_latency(target)
            
            output = f"Multi-Region Latency for {target}:\n\n"
            for region, data in results.items():
                output += f"{region}:\n"
                if 'error' in data:
                    output += f"  Error: {data['error']}\n"
                else:
                    lat = data['latency_ms']
                    output += f"  Average: {lat['avg']:.2f} ms\n"
                    output += f"  Packet Loss: {data['packet_loss']:.1f}%\n"
                output += "\n"
            
            self.trace_results.setText(output)
            self.status_label.setText(f"Multi-region latency complete for {target}")
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Multi-region latency failed: {str(e)}")
    
    def scan_exposed_files(self):
        url = self.vuln_url.text().strip()
        if not url:
            QMessageBox.warning(self, "Warning", "Please enter a URL")
            return
        
        try:
            from urllib.parse import urlparse
            base_url = f"{urlparse(url).scheme}://{urlparse(url).netloc}"
            
            results = self.vulnerability_scanner.scan_exposed_files(base_url)
            
            output = f"Exposed Files Scan for {base_url}:\n\n"
            if not results:
                output += "No exposed files found.\n"
            else:
                for vuln in results:
                    output += f"Path: {vuln['path']}\n"
                    output += f"URL: {vuln['url']}\n"
                    output += f"Status: {vuln['status_code']}\n"
                    output += f"Severity: {vuln['severity']}\n\n"
            
            self.vuln_results.setText(output)
            self.status_label.setText(f"Exposed files scan complete for {base_url}")
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Exposed files scan failed: {str(e)}")
    
    def scan_security_headers(self):
        url = self.vuln_url.text().strip()
        if not url:
            QMessageBox.warning(self, "Warning", "Please enter a URL")
            return
        
        try:
            result = self.vulnerability_scanner.scan_security_headers(url)
            
            output = f"Security Headers Scan for {url}:\n\n"
            output += f"Present Headers:\n"
            for header, value in result['present_headers'].items():
                output += f"  {header}: {value}\n"
            
            output += f"\nMissing Headers:\n"
            for header in result['missing_headers']:
                output += f"  {header}\n"
            
            output += f"\nSecurity Score: {result['security_score']:.1f}%\n"
            
            self.vuln_results.setText(output)
            self.status_label.setText(f"Security headers scan complete for {url}")
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Security headers scan failed: {str(e)}")
    
    def scan_admin_panels(self):
        url = self.vuln_url.text().strip()
        if not url:
            QMessageBox.warning(self, "Warning", "Please enter a URL")
            return
        
        try:
            from urllib.parse import urlparse
            base_url = f"{urlparse(url).scheme}://{urlparse(url).netloc}"
            
            results = self.vulnerability_scanner.scan_admin_panels(base_url)
            
            output = f"Admin Panel Scan for {base_url}:\n\n"
            if not results:
                output += "No admin panels found.\n"
            else:
                for panel in results:
                    output += f"Path: {panel['path']}\n"
                    output += f"URL: {panel['url']}\n"
                    output += f"Status: {panel['status_code']}\n"
                    output += f"Severity: {panel['severity']}\n\n"
            
            self.vuln_results.setText(output)
            self.status_label.setText(f"Admin panel scan complete for {base_url}")
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Admin panel scan failed: {str(e)}")
    
    def full_vulnerability_scan(self):
        url = self.vuln_url.text().strip()
        if not url:
            QMessageBox.warning(self, "Warning", "Please enter a URL")
            return
        
        try:
            results = self.vulnerability_scanner.full_scan(url)
            
            output = f"Full Vulnerability Scan for {url}:\n\n"
            
            output += "=== Exposed Files ===\n"
            for vuln in results['exposed_files']:
                output += f"{vuln['path']} ({vuln['severity']})\n"
            
            output += "\n=== Security Headers ===\n"
            output += f"Missing: {', '.join(results['security_headers']['missing_headers'])}\n"
            output += f"Score: {results['security_headers']['security_score']:.1f}%\n"
            
            output += "\n=== Admin Panels ===\n"
            for panel in results['admin_panels']:
                output += f"{panel['path']} ({panel['severity']})\n"
            
            self.vuln_results.setText(output)
            self.status_label.setText(f"Full vulnerability scan complete for {url}")
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Full vulnerability scan failed: {str(e)}")
    
    def search_social_media(self):
        query = self.social_query.text().strip()
        if not query:
            QMessageBox.warning(self, "Warning", "Please enter a search query")
            return
        
        reddit_id = self.reddit_client_id.text().strip() or None
        reddit_secret = self.reddit_client_secret.text().strip() or None
        
        try:
            self.social_media_searcher = SocialMediaSearcher(
                reddit_client_id=reddit_id,
                reddit_client_secret=reddit_secret
            )
            
            results = self.social_media_searcher.search_all(query)
            
            output = f"Social Media Search for '{query}':\n\n"
            
            for platform, data in results.items():
                output += f"=== {platform.upper()} ===\n"
                if 'error' in data[0]:
                    output += f"Error: {data[0]['error']}\n"
                else:
                    for item in data[:5]:  # Show first 5 results
                        output += f"Title: {item.get('title', item.get('content', 'N/A')[:50])}\n"
                        output += f"URL: {item.get('url', item.get('permalink', 'N/A'))}\n"
                        output += f"Score: {item.get('score', item.get('reblogs_count', 'N/A'))}\n\n"
            
            self.social_results.setText(output)
            self.status_label.setText(f"Social media search complete for '{query}'")
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Social media search failed: {str(e)}")
    
    def discover_backlinks(self):
        url = self.backlink_url.text().strip()
        if not url:
            QMessageBox.warning(self, "Warning", "Please enter a URL")
            return
        
        try:
            results = self.backlink_discovery.discover_backlinks(url)
            
            output = f"Backlink Discovery for {url}:\n\n"
            
            if 'error' in results[0]:
                output += f"Error: {results[0]['error']}\n"
            else:
                analysis = self.backlink_discovery.analyze_backlinks(results)
                output += f"Total Backlinks: {analysis['total_backlinks']}\n"
                output += f"Unique Domains: {analysis['unique_domains']}\n\n"
                
                output += "Domains:\n"
                for domain in analysis['domains'][:10]:
                    output += f"  {domain}\n"
                
                output += "\nRecent Backlinks:\n"
                for bl in results[:5]:
                    output += f"  {bl['url']} ({bl['timestamp']})\n"
            
            self.backlink_results.setText(output)
            self.status_label.setText(f"Backlink discovery complete for {url}")
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Backlink discovery failed: {str(e)}")
    
    def correlate_osint(self):
        target = self.osint_target.text().strip()
        if not target:
            QMessageBox.warning(self, "Warning", "Please enter a target (IP or domain)")
            return
        
        shodan_key = self.shodan_key.text().strip() or None
        vt_key = self.virustotal_key.text().strip() or None
        abuse_key = self.abuseipdb_key.text().strip() or None
        
        try:
            self.passive_osint = PassiveOSINT(
                shodan_api_key=shodan_key,
                virustotal_api_key=vt_key,
                abuseipdb_api_key=abuse_key
            )
            
            results = self.passive_osint.correlate_osint(target)
            
            output = f"Passive OSINT Correlation for {target}:\n\n"
            
            for source, data in results.items():
                output += f"=== {source.upper()} ===\n"
                if 'error' in data:
                    output += f"Error: {data['error']}\n"
                else:
                    output += f"Data retrieved successfully\n"
                    if source == 'shodan':
                        output += f"ISP: {data.get('isp', 'N/A')}\n"
                        output += f"Open Ports: {len(data.get('ports', []))}\n"
                    elif source == 'virustotal':
                        stats = data.get('data', {}).get('attributes', {})
                        output += f"Reputation: {stats.get('reputation', 'N/A')}\n"
                        output += f"Malicious: {stats.get('last_analysis_stats', {}).get('malicious', 0)}\n"
                output += "\n"
            
            self.osint_results.setText(output)
            self.status_label.setText(f"OSINT correlation complete for {target}")
        except Exception as e:
            QMessageBox.critical(self, "Error", f"OSINT correlation failed: {str(e)}")
    
    def link_knowledge_graph(self):
        text = self.kg_text.toPlainText().strip()
        if not text:
            QMessageBox.warning(self, "Warning", "Please enter text to analyze")
            return
        
        try:
            results = self.knowledge_graph_linker.link_entities(text)
            
            output = "Knowledge Graph Linking:\n\n"
            
            for entity, data in results.items():
                output += f"=== {entity} ===\n"
                
                output += "Wikidata:\n"
                for item in data['wikidata'][:3]:
                    if 'error' not in item:
                        output += f"  {item['label']}: {item['url']}\n"
                
                output += "\nDBpedia:\n"
                for item in data['dbpedia'][:3]:
                    if 'error' not in item:
                        output += f"  {item['label']}: {item['entity']}\n"
                
                output += "\n"
            
            self.kg_results.setText(output)
            self.status_label.setText("Knowledge graph linking complete")
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Knowledge graph linking failed: {str(e)}")

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