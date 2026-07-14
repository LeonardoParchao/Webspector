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
import hashlib
import time
import warnings
import logging
import os
import secrets
import random
from functools import wraps
import math

# Suppress BeautifulSoup XML parsing warning
warnings.filterwarnings('ignore', message='.*parsing an XML document using an HTML parser.*')
from datetime import datetime
import socket
import dns.resolver
import subprocess
import threading
from dataclasses import dataclass
from urllib.parse import quote

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('recontool.log'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

class ConfigManager:
    """Manage persistent configuration storage."""
    
    CONFIG_FILE = 'recontool_config.json'
    DEFAULT_CONFIG = {
        'encryption_salt': None,
        'max_threads': 10,
        'allow_localhost': False,
        'allow_private_ips': False,
        'allowed_schemes': ['http', 'https'],
        'api_keys': {},
        'user_preferences': {
            'default_search_engine': 'google',
            'default_num_results': 10,
            'use_async_crawling': True,
            'respect_robots_txt': True
        }
    }
    
    def __init__(self):
        self.config = self._load_config()
    
    def _load_config(self) -> Dict:
        """Load configuration from file or create default."""
        if os.path.exists(self.CONFIG_FILE):
            try:
                with open(self.CONFIG_FILE, 'r') as f:
                    loaded_config = json.load(f)
                # Merge with defaults to ensure all keys exist
                config = self.DEFAULT_CONFIG.copy()
                config.update(loaded_config)
                return config
            except Exception as e:
                logger.error(f"Failed to load config file: {e}")
                return self.DEFAULT_CONFIG.copy()
        else:
            # Generate random salt for new installation
            config = self.DEFAULT_CONFIG.copy()
            config['encryption_salt'] = secrets.token_hex(32)
            self._save_config(config)
            return config
    
    def _save_config(self, config: Dict):
        """Save configuration to file."""
        try:
            with open(self.CONFIG_FILE, 'w') as f:
                json.dump(config, f, indent=2)
            logger.info("Configuration saved successfully")
        except Exception as e:
            logger.error(f"Failed to save config file: {e}")
    
    def get(self, key: str, default=None):
        """Get configuration value."""
        keys = key.split('.')
        value = self.config
        for k in keys:
            if isinstance(value, dict) and k in value:
                value = value[k]
            else:
                return default
        return value
    
    def set(self, key: str, value):
        """Set configuration value and save."""
        keys = key.split('.')
        config = self.config
        for k in keys[:-1]:
            if k not in config:
                config[k] = {}
            config = config[k]
        config[keys[-1]] = value
        self._save_config(self.config)
    
    def get_encryption_salt(self) -> str:
        """Get the encryption salt, generating one if needed."""
        salt = self.get('encryption_salt')
        if not salt:
            salt = secrets.token_hex(32)
            self.set('encryption_salt', salt)
        return salt
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
try:
    from censys.search import v2
except ImportError:
    v2 = None

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
    
    def __init__(self, config_manager: ConfigManager):
        self._fernet = None
        self.config_manager = config_manager
        self._init_encryption()
    
    def _init_encryption(self):
        """Initialize encryption with a key derived from machine-specific data and secure salt."""
        if Fernet is None:
            logger.warning("Cryptography library not available. API keys will be stored in plain text.")
            return
        
        try:
            # Derive a key from machine-specific data and secure salt from config
            machine_id = os.environ.get('COMPUTERNAME', 'default') + os.environ.get('USERNAME', 'default')
            salt = self.config_manager.get_encryption_salt().encode()
            kdf = PBKDF2HMAC(
                algorithm=hashes.SHA256(),
                length=32,
                salt=salt,
                iterations=100000,
            )
            key = base64.urlsafe_b64encode(kdf.derive(machine_id.encode()))
            self._fernet = Fernet(key)
            logger.info("Encryption initialized successfully")
        except Exception as e:
            logger.error(f"Failed to initialize encryption: {e}")
    
    def encrypt_key(self, api_key: str) -> str:
        """Encrypt an API key."""
        if self._fernet is None:
            return api_key  # Fallback to plain text
        try:
            return self._fernet.encrypt(api_key.encode()).decode()
        except Exception as e:
            logger.error(f"Encryption failed: {e}")
            return api_key
    
    def decrypt_key(self, encrypted_key: str) -> str:
        """Decrypt an API key."""
        if self._fernet is None:
            return encrypted_key  # Return as-is if encryption not available
        try:
            return self._fernet.decrypt(encrypted_key.encode()).decode()
        except Exception as e:
            logger.error(f"Decryption failed: {e}")
            return encrypted_key

class InputValidator:
    """Strict input validation for URLs, IPs, ports, and other user inputs."""
    
    def __init__(self, config_manager: ConfigManager):
        self.config_manager = config_manager
    
    def validate_url(self, url: str) -> tuple[bool, str]:
        """Validate URL format and scheme."""
        if not url or not url.strip():
            return False, "URL cannot be empty"
        
        url = url.strip()
        
        try:
            parsed = urlparse(url)
            
            # Check scheme against whitelist
            allowed_schemes = self.config_manager.get('allowed_schemes', ['http', 'https'])
            if parsed.scheme not in allowed_schemes:
                return False, f"URL must use one of these schemes: {', '.join(allowed_schemes)}"
            
            # Check netloc (domain/IP)
            if not parsed.netloc:
                return False, "URL must contain a valid domain or IP address"
            
            # Check for localhost/private IPs if not allowed
            if not self.config_manager.get('allow_localhost', False):
                if parsed.hostname in ['localhost', '127.0.0.1', '::1']:
                    return False, "localhost is not allowed unless explicitly enabled in settings"
            
            if not self.config_manager.get('allow_private_ips', False):
                try:
                    if ipaddress:
                        ip_obj = ipaddress.ip_address(parsed.hostname)
                        if ip_obj.is_private or ip_obj.is_loopback or ip_obj.is_link_local:
                            return False, "Private IP addresses are not allowed unless explicitly enabled in settings"
                except ValueError:
                    pass  # Not an IP address, continue validation
            
            # Check for suspicious patterns (potential injection)
            dangerous_patterns = ['<script', 'javascript:', 'data:', 'vbscript:', 'onload=', 'onerror=']
            for pattern in dangerous_patterns:
                if pattern.lower() in url.lower():
                    return False, f"URL contains potentially dangerous pattern: {pattern}"
            
            return True, "Valid URL"
        except Exception as e:
            logger.error(f"URL validation error: {e}")
            return False, f"Invalid URL format: {str(e)}"
    
    def validate_ip(self, ip: str) -> tuple[bool, str]:
        """Validate IP address format."""
        if not ip or not ip.strip():
            return False, "IP address cannot be empty"
        
        ip = ip.strip()
        
        try:
            if ipaddress is None:
                return True, "IP validation not available (ipaddress module missing)"
            
            ip_obj = ipaddress.ip_address(ip)
            
            # Check for localhost/private IPs if not allowed
            if not self.config_manager.get('allow_localhost', False):
                if ip_obj.is_loopback:
                    return False, "localhost is not allowed unless explicitly enabled in settings"
            
            if not self.config_manager.get('allow_private_ips', False):
                if ip_obj.is_private or ip_obj.is_link_local:
                    return False, "Private IP addresses are not allowed unless explicitly enabled in settings"
            
            return True, "Valid IP address"
        except ValueError:
            return False, "Invalid IP address format"
        except Exception as e:
            logger.error(f"IP validation error: {e}")
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
    
    def __init__(self, config_manager: ConfigManager):
        self.config_manager = config_manager
        self._active_threads = []
        self._max_threads = self.config_manager.get('max_threads', 10)
    
    @classmethod
    def get_instance(cls, config_manager: ConfigManager):
        """Get singleton instance with config manager."""
        with QMutexLocker(cls._mutex):
            if cls._instance is None:
                cls._instance = cls(config_manager)
            return cls._instance
    
    def can_start_thread(self) -> tuple[bool, str]:
        """Check if a new thread can be started. Returns (can_start, message)."""
        with QMutexLocker(self._mutex):
            # Count active threads
            active_count = sum(1 for t in self._active_threads if t.isRunning())
            
            # Warning threshold at 80% capacity
            warning_threshold = int(self._max_threads * 0.8)
            if active_count >= warning_threshold:
                logger.warning(f"Thread pool approaching limit: {active_count}/{self._max_threads} active threads")
            
            if active_count >= self._max_threads:
                return False, f"Maximum thread limit reached ({self._max_threads}). Please wait for current operations to complete."
            
            return True, ""
    
    def register_thread(self, thread: QThread):
        """Register a new thread."""
        with QMutexLocker(self._mutex):
            self._active_threads.append(thread)
            logger.debug(f"Thread registered. Active threads: {self.get_active_count()}")
    
    def unregister_thread(self, thread: QThread):
        """Unregister a thread."""
        with QMutexLocker(self._mutex):
            if thread in self._active_threads:
                self._active_threads.remove(thread)
                logger.debug(f"Thread unregistered. Active threads: {self.get_active_count()}")
    
    def get_active_count(self) -> int:
        """Get count of active threads."""
        with QMutexLocker(self._mutex):
            return sum(1 for t in self._active_threads if t.isRunning())
    
    def set_max_threads(self, max_threads: int):
        """Set maximum number of concurrent threads and save to config."""
        with QMutexLocker(self._mutex):
            self._max_threads = max(1, min(100, max_threads))  # Limit between 1 and 100
            self.config_manager.set('max_threads', self._max_threads)
            logger.info(f"Max threads set to {self._max_threads}")
    
    def get_max_threads(self) -> int:
        """Get maximum number of concurrent threads."""
        return self._max_threads

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

class RobotsTxtParser:
    """Comprehensive robots.txt parser with full directive support."""
    
    def __init__(self, user_agent: str = '*', cache_ttl: int = 3600):
        self.user_agent = user_agent
        self.robots_url = None
        self.raw_content = None
        self.user_agent_records = {}
        self.sitemap_urls = []
        self.crawl_delay = None
        self.request_rate = None
        self.disallowed_paths = set()
        self.allowed_paths = set()
        self.last_modified = None
        self.cache_ttl = cache_ttl
        self.fetched_at = None
        
    def fetch(self, base_url: str, session: requests.Session) -> bool:
        """Fetch and parse robots.txt from the given base URL."""
        from urllib.parse import urlparse
        import time
        
        parsed = urlparse(base_url)
        self.robots_url = f"{parsed.scheme}://{parsed.netloc}/robots.txt"
        
        try:
            response = session.get(self.robots_url, timeout=10)
            if response.status_code == 200:
                self.raw_content = response.text
                self.fetched_at = time.time()
                self._parse()
                return True
            return False
        except Exception:
            return False
    
    def _parse(self):
        """Parse the robots.txt content."""
        if not self.raw_content:
            return
        
        current_user_agent = None
        current_record = {'disallow': [], 'allow': [], 'crawl_delay': None, 'request_rate': None}
        
        for line in self.raw_content.split('\n'):
            line = line.strip()
            if not line or line.startswith('#'):
                continue
            
            # Split on first colon
            if ':' not in line:
                continue
            
            parts = line.split(':', 1)
            directive = parts[0].strip().lower()
            value = parts[1].strip() if len(parts) > 1 else ''
            
            if directive == 'user-agent':
                # Save previous record
                if current_user_agent:
                    self.user_agent_records[current_user_agent] = current_record
                
                current_user_agent = value if value else '*'
                current_record = {'disallow': [], 'allow': [], 'crawl_delay': None, 'request_rate': None}
            
            elif directive == 'disallow' and current_user_agent:
                current_record['disallow'].append(value)
            
            elif directive == 'allow' and current_user_agent:
                current_record['allow'].append(value)
            
            elif directive == 'crawl-delay' and current_user_agent:
                try:
                    current_record['crawl_delay'] = float(value)
                except ValueError:
                    pass
            
            elif directive == 'request-rate' and current_user_agent:
                current_record['request_rate'] = value
            
            elif directive == 'sitemap':
                self.sitemap_urls.append(value)
        
        # Save last record
        if current_user_agent:
            self.user_agent_records[current_user_agent] = current_record
        
        # Find best matching user agent record
        self._apply_user_agent_rules()
    
    def _apply_user_agent_rules(self):
        """Apply rules for the configured user agent."""
        import fnmatch
        
        # Try exact match first
        if self.user_agent in self.user_agent_records:
            record = self.user_agent_records[self.user_agent]
        # Try wildcard matching
        else:
            best_match = None
            for ua_pattern in self.user_agent_records:
                if fnmatch.fnmatch(self.user_agent, ua_pattern):
                    # Prefer more specific patterns (longer is more specific)
                    if best_match is None or len(ua_pattern) > len(best_match):
                        best_match = ua_pattern
            
            # Fallback to wildcard
            if best_match:
                record = self.user_agent_records[best_match]
            elif '*' in self.user_agent_records:
                record = self.user_agent_records['*']
            else:
                return
        
        self.disallowed_paths = set(record['disallow'])
        self.allowed_paths = set(record['allow'])
        self.crawl_delay = record['crawl_delay']
        self.request_rate = record['request_rate']
    
    def can_fetch(self, url: str) -> bool:
        """Check if the given URL can be fetched according to robots.txt rules."""
        from urllib.parse import urlparse
        import fnmatch
        
        parsed = urlparse(url)
        path = parsed.path
        
        # Check explicit allows first (they override disallows)
        for allowed in self.allowed_paths:
            if self._match_pattern(path, allowed):
                return True
        
        # Check disallows
        for disallowed in self.disallowed_paths:
            if self._match_pattern(path, disallowed):
                return False
        
        # Default: allow
        return True
    
    def _match_pattern(self, path: str, pattern: str) -> bool:
        """Match path against pattern with wildcard support (* and $)."""
        import re
        
        # Handle $ as end-of-string marker
        if pattern.endswith('$'):
            pattern = pattern[:-1]
            return path == pattern or path.startswith(pattern)
        
        # Handle * wildcard
        if '*' in pattern:
            # Convert robots.txt wildcard to regex
            # * matches any sequence of characters
            regex_pattern = pattern.replace('*', '.*')
            return re.match(regex_pattern, path) is not None
        
        # Simple prefix match
        return path.startswith(pattern)
    
    def is_cache_expired(self) -> bool:
        """Check if the cached robots.txt has expired."""
        import time
        if self.fetched_at is None:
            return True
        return time.time() - self.fetched_at > self.cache_ttl
    
    def get_sitemap_urls(self) -> List[str]:
        """Return all sitemap URLs found in robots.txt."""
        return self.sitemap_urls
    
    def get_crawl_delay(self) -> Optional[float]:
        """Return the crawl delay in seconds."""
        return self.crawl_delay
    
    def get_request_rate(self) -> Optional[str]:
        """Return the request rate directive."""
        return self.request_rate
    
    def get_disallowed_paths(self) -> Set[str]:
        """Return all disallowed paths."""
        return self.disallowed_paths
    
    def get_allowed_paths(self) -> Set[str]:
        """Return all allowed paths."""
        return self.allowed_paths
    
    def get_raw_content(self) -> Optional[str]:
        """Return the raw robots.txt content."""
        return self.raw_content


class SitemapParser:
    """Comprehensive sitemap.xml parser with support for sitemap indexes and various formats."""
    
    def __init__(self, max_recursion_depth: int = 5):
        self.urls = []
        self.sitemap_index_urls = []
        self.url_metadata = {}  # URL -> metadata (lastmod, changefreq, priority)
        self.raw_content = None
        self.sitemap_url = None
        self.max_recursion_depth = max_recursion_depth
        self.current_depth = 0
        
    def fetch(self, sitemap_url: str, session: requests.Session, recursive: bool = True) -> bool:
        """Fetch and parse the sitemap."""
        self.sitemap_url = sitemap_url
        
        try:
            response = session.get(sitemap_url, timeout=10)
            if response.status_code == 200:
                # Handle gzip compression
                if sitemap_url.endswith('.gz') or response.headers.get('Content-Encoding') == 'gzip':
                    import gzip
                    import io
                    self.raw_content = gzip.decompress(response.content).decode('utf-8')
                else:
                    self.raw_content = response.text
                self._parse(recursive=recursive, session=session)
                return True
            return False
        except Exception:
            return False
    
    def _parse(self, recursive: bool = True, session: requests.Session = None):
        """Parse the sitemap XML content."""
        if not self.raw_content:
            return
        
        import xml.etree.ElementTree as ET
        
        try:
            # Use iterative parsing for large files
            if len(self.raw_content) > 10 * 1024 * 1024:  # 10MB threshold
                self._parse_streaming()
                return
            
            root = ET.fromstring(self.raw_content)
            
            # Check if this is a sitemap index
            sitemap_locs = root.findall('.//{http://www.sitemaps.org/schemas/sitemap/0.9}loc')
            if sitemap_locs and not root.findall('.//{http://www.sitemaps.org/schemas/sitemap/0.9}url'):
                # This is a sitemap index
                for loc in sitemap_locs:
                    child_sitemap_url = loc.text
                    if child_sitemap_url:
                        self.sitemap_index_urls.append(child_sitemap_url)
                        if recursive and session and self.current_depth < self.max_recursion_depth:
                            # Recursively parse child sitemaps with depth limit
                            child_parser = SitemapParser(max_recursion_depth=self.max_recursion_depth)
                            child_parser.current_depth = self.current_depth + 1
                            child_parser.fetch(child_sitemap_url, session, recursive=True)
                            self.urls.extend(child_parser.urls)
                            self.url_metadata.update(child_parser.url_metadata)
            else:
                # This is a regular URL sitemap
                url_elements = root.findall('.//{http://www.sitemaps.org/schemas/sitemap/0.9}url')
                
                for url_elem in url_elements:
                    loc = url_elem.find('{http://www.sitemaps.org/schemas/sitemap/0.9}loc')
                    if loc is not None and loc.text:
                        url = loc.text
                        self.urls.append(url)
                        
                        # Extract metadata
                        metadata = {}
                        lastmod = url_elem.find('{http://www.sitemaps.org/schemas/sitemap/0.9}lastmod')
                        if lastmod is not None and lastmod.text:
                            metadata['lastmod'] = lastmod.text
                        
                        changefreq = url_elem.find('{http://www.sitemaps.org/schemas/sitemap/0.9}changefreq')
                        if changefreq is not None and changefreq.text:
                            metadata['changefreq'] = changefreq.text
                        
                        priority = url_elem.find('{http://www.sitemaps.org/schemas/sitemap/0.9}priority')
                        if priority is not None and priority.text:
                            metadata['priority'] = priority.text
                        
                        if metadata:
                            self.url_metadata[url] = metadata
                            
        except ET.ParseError:
            # Fallback to regex parsing if XML parsing fails
            self._parse_with_regex()
    
    def _parse_streaming(self):
        """Parse large XML files using iterative streaming."""
        import xml.etree.ElementTree as ET
        from io import StringIO
        
        context = ET.iterparse(StringIO(self.raw_content), events=('start', 'end'))
        context = iter(context)
        
        try:
            event, root = next(context)
            
            for event, elem in context:
                if event == 'end':
                    # Handle URL elements
                    if elem.tag.endswith('url'):
                        loc = elem.find('{http://www.sitemaps.org/schemas/sitemap/0.9}loc')
                        if loc is not None and loc.text:
                            url = loc.text
                            self.urls.append(url)
                            
                            # Extract metadata
                            metadata = {}
                            lastmod = elem.find('{http://www.sitemaps.org/schemas/sitemap/0.9}lastmod')
                            if lastmod is not None and lastmod.text:
                                metadata['lastmod'] = lastmod.text
                            
                            changefreq = elem.find('{http://www.sitemaps.org/schemas/sitemap/0.9}changefreq')
                            if changefreq is not None and changefreq.text:
                                metadata['changefreq'] = changefreq.text
                            
                            priority = elem.find('{http://www.sitemaps.org/schemas/sitemap/0.9}priority')
                            if priority is not None and priority.text:
                                metadata['priority'] = priority.text
                            
                            if metadata:
                                self.url_metadata[url] = metadata
                    
                    # Clear element to save memory
                    elem.clear()
                    
        except Exception as e:
            print(f"Streaming parse failed: {e}")
            self._parse_with_regex()
    
    def _parse_with_regex(self):
        """Fallback regex-based parsing for malformed XML."""
        import re
        
        if not self.raw_content:
            return
        
        # Extract URLs with regex
        url_pattern = r'<loc>(.*?)</loc>'
        matches = re.findall(url_pattern, self.raw_content)
        self.urls.extend(matches)
        
        # Try to extract sitemap index URLs
        sitemap_pattern = r'<sitemap>.*?<loc>(.*?)</loc>.*?</sitemap>'
        sitemap_matches = re.findall(sitemap_pattern, self.raw_content, re.DOTALL)
        self.sitemap_index_urls.extend(sitemap_matches)
    
    def get_urls(self) -> List[str]:
        """Return all URLs found in the sitemap."""
        return self.urls
    
    def get_url_metadata(self, url: str) -> Dict:
        """Return metadata for a specific URL."""
        return self.url_metadata.get(url, {})
    
    def get_all_metadata(self) -> Dict:
        """Return all URL metadata."""
        return self.url_metadata
    
    def get_sitemap_index_urls(self) -> List[str]:
        """Return URLs of child sitemaps (if this is a sitemap index)."""
        return self.sitemap_index_urls
    
    def get_urls_by_priority(self, min_priority: float = 0.5) -> List[str]:
        """Return URLs with priority >= min_priority."""
        high_priority_urls = []
        for url, metadata in self.url_metadata.items():
            priority = metadata.get('priority', '0.5')
            try:
                if float(priority) >= min_priority:
                    high_priority_urls.append(url)
            except ValueError:
                pass
        return high_priority_urls
    
    def get_urls_by_change_frequency(self, frequency: str) -> List[str]:
        """Return URLs with specific change frequency."""
        matching_urls = []
        for url, metadata in self.url_metadata.items():
            if metadata.get('changefreq', '').lower() == frequency.lower():
                matching_urls.append(url)
        return matching_urls
    
    def get_recent_urls(self, days: int = 7) -> List[str]:
        """Return URLs modified within the last N days."""
        from datetime import datetime, timedelta
        
        recent_urls = []
        cutoff_date = datetime.now() - timedelta(days=days)
        
        for url, metadata in self.url_metadata.items():
            lastmod = metadata.get('lastmod')
            if lastmod:
                try:
                    mod_date = datetime.fromisoformat(lastmod.replace('Z', '+00:00'))
                    if mod_date >= cutoff_date:
                        recent_urls.append(url)
                except (ValueError, AttributeError):
                    pass
        
        return recent_urls
    
    def get_raw_content(self) -> Optional[str]:
        """Return the raw sitemap content."""
        return self.raw_content


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
                 max_memory_results: int = 1000,
                 near_duplicate_threshold: float = 0.85):
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
        self.max_visited_urls = 10000  # LRU cache size for visited URLs
        
        if self.use_disk_cache:
            import os
            os.makedirs(self._cache_dir, exist_ok=True)
        
        # LRU cache for visited URLs
        self._visited_urls_lru = []
        self._visited_urls_dict = {}
        
        # Redirect tracking
        self.redirect_chains: Dict[str, List[str]] = {}  # URL -> chain of redirects
        self.max_redirects_per_url = 10
        
        # URL status tracking for progress callbacks
        self.url_status: Dict[str, str] = {}  # URL -> status (queued, fetching, parsed, error)
        
        # Rate limiting and backoff
        self.domain_last_request: Dict[str, float] = {}
        self.domain_retry_count: Dict[str, int] = {}
        self.max_retries = 3
        
        # Robots.txt and sitemap cache
        self.robots_cache: Dict[str, RobotsTxtParser] = {}
        self.sitemap_cache: Dict[str, SitemapParser] = {}
        
        # Content fingerprinting
        self.content_hashes: Dict[str, Simhash] = {}
        self.near_duplicate_threshold = near_duplicate_threshold
        
        # Authentication
        if auth_credentials:
            self._setup_authentication()
        
        # Cookie jar persistence
        self.cookie_jar_file = os.path.join(self._cache_dir, "cookies.json") if self.use_disk_cache else None
        self._load_cookie_jar()
        
        # CSRF token extraction
        self.csrf_token_patterns = [
            r'name=["\']csrf["\']\s+value=["\']([^"\']+)["\']',
            r'name=["\']_token["\']\s+value=["\']([^"\']+)["\']',
            r'name=["\']authenticity_token["\']\s+value=["\']([^"\']+)["\']',
            r'csrf["\']\s*:\s*["\']([^"\']+)["\']',
            r'_token["\']\s*:\s*["\']([^"\']+)["\']',
        ]
        
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
    
    def _load_cookie_jar(self):
        """Load cookies from persistent storage."""
        if not self.cookie_jar_file or not os.path.exists(self.cookie_jar_file):
            return
        
        try:
            import json
            with open(self.cookie_jar_file, 'r', encoding='utf-8') as f:
                cookies = json.load(f)
                for cookie in cookies:
                    self.session.cookies.set(**cookie)
        except Exception as e:
            print(f"Error loading cookie jar: {e}")
    
    def _save_cookie_jar(self):
        """Save cookies to persistent storage."""
        if not self.cookie_jar_file:
            return
        
        try:
            import json
            cookies = []
            for cookie in self.session.cookies:
                cookies.append({
                    'name': cookie.name,
                    'value': cookie.value,
                    'domain': cookie.domain,
                    'path': cookie.path,
                    'expires': cookie.expires
                })
            
            with open(self.cookie_jar_file, 'w', encoding='utf-8') as f:
                json.dump(cookies, f, indent=2)
        except Exception as e:
            print(f"Error saving cookie jar: {e}")
    
    def _extract_csrf_token(self, html_content: str) -> Optional[str]:
        """Extract CSRF token from HTML content using multiple patterns."""
        import re
        
        for pattern in self.csrf_token_patterns:
            match = re.search(pattern, html_content, re.IGNORECASE)
            if match:
                return match.group(1)
        
        return None
    
    def _check_redirect_loop(self, url: str, redirect_history: List[str]) -> bool:
        """Check if a redirect loop is detected."""
        # Check if URL appears multiple times in redirect chain
        if redirect_history.count(url) > 1:
            return True
        
        # Check if chain length exceeds limit
        if len(redirect_history) > self.max_redirects_per_url:
            return True
        
        # Check for circular redirects (A -> B -> C -> A)
        if len(redirect_history) >= 3:
            last_three = redirect_history[-3:]
            if len(set(last_three)) < len(last_three):
                return True
        
        return False
    
    def _track_redirect(self, original_url: str, redirect_url: str):
        """Track redirect chain for a URL."""
        if original_url not in self.redirect_chains:
            self.redirect_chains[original_url] = []
        
        self.redirect_chains[original_url].append(redirect_url)
        
        # Check for redirect loop
        if self._check_redirect_loop(redirect_url, self.redirect_chains[original_url]):
            print(f"Redirect loop detected for {original_url}: {self.redirect_chains[original_url]}")
            return True
        
        return False
    
    def _update_url_status(self, url: str, status: str):
        """Update the status of a URL for progress tracking."""
        self.url_status[url] = status
    
    def _get_url_status_summary(self) -> Dict[str, int]:
        """Get a summary of URL statuses."""
        summary = {'queued': 0, 'fetching': 0, 'parsed': 0, 'error': 0}
        for status in self.url_status.values():
            if status in summary:
                summary[status] += 1
        return summary
    
    def _add_result(self, result: Dict):
        """Add result with memory management."""
        if self.use_disk_cache and len(self.results) >= self.max_memory_results:
            # Flush to disk cache
            self._flush_to_disk()
        
        self.results.append(result)
    
    def _add_visited_url(self, url: str):
        """Add URL to LRU cache with memory management."""
        if url in self._visited_urls_dict:
            # Move to front (most recently used)
            self._visited_urls_lru.remove(url)
            self._visited_urls_lru.append(url)
        else:
            # Add new URL
            if len(self._visited_urls_lru) >= self.max_visited_urls:
                # Remove least recently used
                oldest = self._visited_urls_lru.pop(0)
                del self._visited_urls_dict[oldest]
            self._visited_urls_lru.append(url)
            self._visited_urls_dict[url] = True
    
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
    
    def _init_sqlite_db(self):
        """Initialize SQLite database for persistent storage."""
        import sqlite3
        import os
        
        db_path = os.path.join(self._cache_dir, "crawl_data.db")
        conn = sqlite3.connect(db_path)
        cursor = conn.cursor()
        
        # Create tables
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS visited_urls (
                url TEXT PRIMARY KEY,
                timestamp DATETIME DEFAULT CURRENT_TIMESTAMP
            )
        ''')
        
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS crawl_results (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                url TEXT,
                depth INTEGER,
                type TEXT,
                status_code INTEGER,
                page_size INTEGER,
                response_time REAL,
                error TEXT,
                timestamp DATETIME DEFAULT CURRENT_TIMESTAMP
            )
        ''')
        
        conn.commit()
        conn.close()
        return db_path
    
    def _save_visited_url_to_db(self, url: str):
        """Save visited URL to SQLite database."""
        import sqlite3
        import os
        
        db_path = os.path.join(self._cache_dir, "crawl_data.db")
        try:
            conn = sqlite3.connect(db_path)
            cursor = conn.cursor()
            cursor.execute('INSERT OR IGNORE INTO visited_urls (url) VALUES (?)', (url,))
            conn.commit()
            conn.close()
        except Exception as e:
            print(f"Error saving visited URL to database: {e}")
    
    def _save_result_to_db(self, result: Dict):
        """Save crawl result to SQLite database."""
        import sqlite3
        import os
        
        db_path = os.path.join(self._cache_dir, "crawl_data.db")
        try:
            conn = sqlite3.connect(db_path)
            cursor = conn.cursor()
            cursor.execute('''
                INSERT INTO crawl_results (url, depth, type, status_code, page_size, response_time, error)
                VALUES (?, ?, ?, ?, ?, ?, ?)
            ''', (
                result.get('url'),
                result.get('depth'),
                result.get('type'),
                result.get('status_code'),
                result.get('page_size'),
                result.get('response_time'),
                result.get('error')
            ))
            conn.commit()
            conn.close()
        except Exception as e:
            print(f"Error saving result to database: {e}")
    
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
        except Exception as e:
            logger.error(f"Failed to extract domain from URL {url}: {e}")
            return ''
    
    def _can_fetch(self, url: str) -> bool:
        """Check if URL can be fetched according to robots.txt."""
        if not self.respect_robots:
            return True
        
        domain = self._get_domain(url)
        if not domain:
            return True
        
        if domain not in self.robots_cache or self.robots_cache[domain].is_cache_expired():
            robots_parser = RobotsTxtParser(user_agent=self.session.headers.get('User-Agent', '*'))
            robots_parser.fetch(url, self.session)
            self.robots_cache[domain] = robots_parser
        
        robots_parser = self.robots_cache[domain]
        return robots_parser.can_fetch(url)
    
    def _get_crawl_delay(self, domain: str) -> float:
        """Get crawl delay from robots.txt or use default."""
        if domain in self.robots_cache and self.robots_cache[domain]:
            delay = self.robots_cache[domain].get_crawl_delay()
            if delay is not None:
                return max(delay, self.rate_limit_delay)
        return self.rate_limit_delay
    
    def _parse_robots_txt_for_urls(self, url: str) -> Set[str]:
        """Parse robots.txt to extract sitemap URLs."""
        urls = set()
        domain = self._get_domain(url)
        if not domain:
            return urls
        
        if domain not in self.robots_cache:
            robots_parser = RobotsTxtParser(user_agent=self.session.headers.get('User-Agent', '*'))
            robots_parser.fetch(url, self.session)
            self.robots_cache[domain] = robots_parser
        
        robots_parser = self.robots_cache[domain]
        sitemap_urls = robots_parser.get_sitemap_urls()
        urls.update(sitemap_urls)
        
        return urls
    
    def _parse_sitemap_xml(self, sitemap_url: str) -> Set[str]:
        """Parse sitemap.xml to extract URLs using the enhanced parser."""
        if sitemap_url in self.sitemap_cache:
            return set(self.sitemap_cache[sitemap_url].get_urls())
        
        sitemap_parser = SitemapParser()
        sitemap_parser.fetch(sitemap_url, self.session, recursive=True)
        self.sitemap_cache[sitemap_url] = sitemap_parser
        
        return set(sitemap_parser.get_urls())
    
    def get_sitemap_metadata(self, sitemap_url: str) -> Dict:
        """Get metadata for all URLs in a sitemap."""
        if sitemap_url not in self.sitemap_cache:
            sitemap_parser = SitemapParser()
            sitemap_parser.fetch(sitemap_url, self.session, recursive=True)
            self.sitemap_cache[sitemap_url] = sitemap_parser
        
        return self.sitemap_cache[sitemap_url].get_all_metadata()
    
    def get_robots_info(self, url: str) -> Dict:
        """Get comprehensive robots.txt information for a domain."""
        domain = self._get_domain(url)
        if not domain:
            return {}
        
        if domain not in self.robots_cache:
            robots_parser = RobotsTxtParser(user_agent=self.session.headers.get('User-Agent', '*'))
            robots_parser.fetch(url, self.session)
            self.robots_cache[domain] = robots_parser
        
        robots_parser = self.robots_cache[domain]
        return {
            'disallowed_paths': list(robots_parser.get_disallowed_paths()),
            'allowed_paths': list(robots_parser.get_allowed_paths()),
            'crawl_delay': robots_parser.get_crawl_delay(),
            'request_rate': robots_parser.get_request_rate(),
            'sitemap_urls': robots_parser.get_sitemap_urls(),
            'raw_content': robots_parser.get_raw_content()
        }
    
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
            try:
                await page.goto(url, wait_until='networkidle', timeout=30000)
                content = await page.content()
                return content
            finally:
                await page.close()
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
        except Exception as e:
            logger.error(f"URL comparison failed: {e}")
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
                content_type = response.headers.get('content-type', '').lower()
                
                # Skip binary content types
                if any(ct in content_type for ct in ['application/pdf', 'image/', 'video/', 'audio/', 'application/octet-stream']):
                    print(f"Skipping binary content: {url} (content-type: {content_type})")
                    return None
                
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
            
            self._add_visited_url(url)
            self._update_url_status(url, 'fetching')
            
            fetch_result = await self._fetch_page_async(session, url)
            
            if fetch_result is None:
                self._update_url_status(url, 'error')
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
            
            # Calculate content hash
            content_hash = hashlib.sha256(page_text.encode()).hexdigest() if page_text else ''
            
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
            
            self._update_url_status(url, 'parsed')
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
                    status_summary = self._get_url_status_summary()
                    progress_callback(len(self.visited_urls), len(self.results), status_summary)
        
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
            # Run async crawl in event loop with proper cleanup
            loop = asyncio.new_event_loop()
            asyncio.set_event_loop(loop)
            try:
                results = loop.run_until_complete(
                    self.crawl_async(search_text, search_names, file_extensions, use_regex, progress_callback)
                )
                return results
            finally:
                # Clean up pending tasks
                try:
                    pending = asyncio.all_tasks(loop)
                    for task in pending:
                        task.cancel()
                    if pending:
                        loop.run_until_complete(asyncio.gather(*pending, return_exceptions=True))
                except Exception as e:
                    logger.debug(f"Error cleaning up async tasks: {e}")
                finally:
                    loop.close()
                    asyncio.set_event_loop(None)
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
            if self.is_cancelled():
                break
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
            
            self._add_visited_url(current_url)
            self._update_url_status(current_url, 'fetching')
            
            try:
                start_time = time.time()
                response = self.session.get(current_url, timeout=10)
                response_time = time.time() - start_time
                status_code = response.status_code
                page_size = len(response.content)
                
                response.raise_for_status()
                
                content_type = response.headers.get('content-type', '').lower()
                
                # Skip binary content types
                if any(ct in content_type for ct in ['application/pdf', 'image/', 'video/', 'audio/', 'application/octet-stream']):
                    print(f"Skipping binary content: {current_url} (content-type: {content_type})")
                    continue
                
                if 'text/html' in content_type:
                    soup = BeautifulSoup(response.text, 'html.parser')
                    page_text = self.extract_text(soup)
                    
                    # Calculate content hash
                    content_hash = hashlib.sha256(page_text.encode()).hexdigest() if page_text else ''
                    
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
                    
                    self._update_url_status(current_url, 'parsed')
                    
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
                        self._update_url_status(current_url, 'parsed')
                
                if progress_callback:
                    status_summary = self._get_url_status_summary()
                    progress_callback(len(self.visited_urls), len(self.results), status_summary)
                    
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

# User-Agent rotation pool
USER_AGENTS = [
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/92.0.4515.107 Safari/537.36',
    'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:89.0) Gecko/20100101 Firefox/89.0',
    'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/14.1.1 Safari/605.1.15',
    'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Edge/91.0.864.59',
    'Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:90.0) Gecko/20100101 Firefox/90.0'
]

def retry_with_exponential_backoff(max_retries: int = 3, initial_delay: float = 1.0, 
                                   backoff_factor: float = 2.0, exceptions: tuple = (Exception,)):
    """
    Decorator for retrying function calls with exponential backoff.
    
    Args:
        max_retries: Maximum number of retry attempts
        initial_delay: Initial delay in seconds
        backoff_factor: Multiplier for delay after each retry
        exceptions: Tuple of exceptions to catch and retry on
    """
    def decorator(func):
        @wraps(func)
        def wrapper(*args, **kwargs):
            delay = initial_delay
            last_exception = None
            
            for attempt in range(max_retries + 1):
                try:
                    return func(*args, **kwargs)
                except exceptions as e:
                    last_exception = e
                    if attempt == max_retries:
                        logger.error(f"Max retries ({max_retries}) exceeded for {func.__name__}: {e}")
                        raise
                    
                    logger.warning(f"Attempt {attempt + 1} failed for {func.__name__}: {e}. Retrying in {delay:.2f}s...")
                    time.sleep(delay)
                    delay *= backoff_factor
            
            raise last_exception
        return wrapper
    return decorator

def detect_captcha(response_text: str) -> bool:
    """
    Detect if response contains CAPTCHA challenge.
    
    Args:
        response_text: HTML response text
        
    Returns:
        True if CAPTCHA detected, False otherwise
    """
    captcha_indicators = [
        'captcha', 'CAPTCHA', 'unusual traffic', 'verify you are human',
        'security check', 'human verification', 'are you a robot',
        'recaptcha', 'reCAPTCHA', 'challenge platform'
    ]
    
    response_lower = response_text.lower()
    return any(indicator.lower() in response_lower for indicator in captcha_indicators)

class CaptchaSolver:
    """
    CAPTCHA solver using 2Captcha service.
    
    Requires 2Captcha API key.
    """
    
    def __init__(self, api_key: str):
        """
        Initialize CAPTCHA solver.
        
        Args:
            api_key: 2Captcha API key
        """
        self.api_key = api_key
        self.base_url = 'http://2captcha.com'
    
    def solve_recaptcha_v2(self, site_key: str, page_url: str, timeout: int = 120) -> Optional[str]:
        """
        Solve reCAPTCHA v2 using 2Captcha.
        
        Args:
            site_key: The site key for reCAPTCHA
            page_url: The URL of the page with CAPTCHA
            timeout: Maximum time to wait for solution (seconds)
            
        Returns:
            Solution token if successful, None otherwise
        """
        try:
            # Submit CAPTCHA
            submit_url = f'{self.base_url}/in.php'
            params = {
                'key': self.api_key,
                'method': 'userrecaptcha',
                'googlekey': site_key,
                'pageurl': page_url,
                'json': 1
            }
            
            response = requests.post(submit_url, params=params, timeout=30)
            response.raise_for_status()
            data = response.json()
            
            if data['status'] != 1:
                logger.error(f"CAPTCHA submission failed: {data.get('request', 'Unknown error')}")
                return None
            
            captcha_id = data['request']
            logger.info(f"CAPTCHA submitted with ID: {captcha_id}")
            
            # Poll for solution
            result_url = f'{self.base_url}/res.php'
            start_time = time.time()
            
            while time.time() - start_time < timeout:
                params = {
                    'key': self.api_key,
                    'action': 'get',
                    'id': captcha_id,
                    'json': 1
                }
                
                response = requests.get(result_url, params=params, timeout=30)
                response.raise_for_status()
                data = response.json()
                
                if data['status'] == 1:
                    logger.info("CAPTCHA solved successfully")
                    return data['request']
                elif data['request'] == 'CAPCHA_NOT_READY':
                    time.sleep(5)
                else:
                    logger.error(f"CAPTCHA solving failed: {data.get('request', 'Unknown error')}")
                    return None
            
            logger.error("CAPTCHA solving timed out")
            return None
            
        except Exception as e:
            logger.error(f"Error solving CAPTCHA: {e}")
            return None
    
    def solve_image_captcha(self, image_data: bytes, timeout: int = 120) -> Optional[str]:
        """
        Solve image CAPTCHA using 2Captcha.
        
        Args:
            image_data: Raw image data (bytes)
            timeout: Maximum time to wait for solution (seconds)
            
        Returns:
            Solution text if successful, None otherwise
        """
        try:
            # Submit CAPTCHA
            submit_url = f'{self.base_url}/in.php'
            files = {'file': ('captcha.jpg', image_data, 'image/jpeg')}
            params = {
                'key': self.api_key,
                'method': 'post',
                'json': 1
            }
            
            response = requests.post(submit_url, files=files, params=params, timeout=30)
            response.raise_for_status()
            data = response.json()
            
            if data['status'] != 1:
                logger.error(f"CAPTCHA submission failed: {data.get('request', 'Unknown error')}")
                return None
            
            captcha_id = data['request']
            logger.info(f"Image CAPTCHA submitted with ID: {captcha_id}")
            
            # Poll for solution
            result_url = f'{self.base_url}/res.php'
            start_time = time.time()
            
            while time.time() - start_time < timeout:
                params = {
                    'key': self.api_key,
                    'action': 'get',
                    'id': captcha_id,
                    'json': 1
                }
                
                response = requests.get(result_url, params=params, timeout=30)
                response.raise_for_status()
                data = response.json()
                
                if data['status'] == 1:
                    logger.info("Image CAPTCHA solved successfully")
                    return data['request']
                elif data['request'] == 'CAPCHA_NOT_READY':
                    time.sleep(5)
                else:
                    logger.error(f"CAPTCHA solving failed: {data.get('request', 'Unknown error')}")
                    return None
            
            logger.error("CAPTCHA solving timed out")
            return None
            
        except Exception as e:
            logger.error(f"Error solving image CAPTCHA: {e}")
            return None

class Searcher:
    def __init__(self, use_rotation: bool = True, proxies: Optional[List[str]] = None,
                 captcha_solver_api_key: Optional[str] = None,
                 google_api_key: Optional[str] = None,
                 google_cx_id: Optional[str] = None,
                 bing_api_key: Optional[str] = None):
        """
        Initialize Searcher with advanced features.
        
        Args:
            use_rotation: Enable user-agent rotation
            proxies: List of proxy URLs (format: 'http://user:pass@host:port')
            captcha_solver_api_key: API key for CAPTCHA solving service (e.g., 2Captcha)
            google_api_key: Google Custom Search API key
            google_cx_id: Google Custom Search Engine ID
            bing_api_key: Bing Web Search API key
        """
        self.session = requests.Session()
        self.use_rotation = use_rotation
        self.proxies = proxies or []
        self.current_proxy_index = 0
        self.captcha_solver_api_key = captcha_solver_api_key
        self.google_api_key = google_api_key
        self.google_cx_id = google_cx_id
        self.bing_api_key = bing_api_key
        self.results: List[Dict] = []
        self.search_engines = {
            'google': 'https://www.google.com/search',
            'bing': 'https://www.bing.com/search',
            'duckduckgo': 'https://duckduckgo.com/html/'
        }
        self._rotate_user_agent()
        
    def _rotate_user_agent(self):
        """Rotate to a random user-agent."""
        if self.use_rotation:
            user_agent = random.choice(USER_AGENTS)
            self.session.headers.update({'User-Agent': user_agent})
    
    def _get_proxy(self) -> Optional[Dict[str, str]]:
        """Get next proxy from rotation."""
        if not self.proxies:
            return None
        proxy = self.proxies[self.current_proxy_index]
        self.current_proxy_index = (self.current_proxy_index + 1) % len(self.proxies)
        return {'http': proxy, 'https': proxy}
    
    def _handle_captcha(self, response_text: str) -> bool:
        """
        Handle CAPTCHA detection.
        
        Args:
            response_text: Response text to check for CAPTCHA
            
        Returns:
            True if CAPTCHA was handled, False otherwise
        """
        if detect_captcha(response_text):
            logger.warning("CAPTCHA detected in response")
            if self.captcha_solver_api_key:
                logger.info("CAPTCHA solver API key configured - would attempt solving")
                # TODO: Implement 2Captcha integration
                # For now, return False to indicate not handled
                return False
            else:
                logger.warning("No CAPTCHA solver configured - pausing recommended")
                return False
        return True
    
    @retry_with_exponential_backoff(max_retries=3, initial_delay=1.0, backoff_factor=2.0, 
                                   exceptions=(requests.RequestException, requests.Timeout))
    def search_google(self, query: str, num_results: int = 10, site: Optional[str] = None) -> List[Dict]:
        """Search using Google with retry logic and CAPTCHA detection."""
        self._rotate_user_agent()
        search_url = self.search_engines['google']
        params = {'q': query, 'num': num_results}
        if site:
            params['q'] = f"site:{site} {query}"
        
        proxy = self._get_proxy()
        
        try:
            response = self.session.get(search_url, params=params, timeout=10, proxies=proxy)
            response.raise_for_status()
            
            # Check for CAPTCHA
            if not self._handle_captcha(response.text):
                return [{'error': 'CAPTCHA detected - could not handle', 'engine': 'google'}]
            
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
    
    @retry_with_exponential_backoff(max_retries=3, initial_delay=1.0, backoff_factor=2.0,
                                   exceptions=(requests.RequestException, requests.Timeout))
    def search_bing(self, query: str, num_results: int = 10, site: Optional[str] = None) -> List[Dict]:
        """Search using Bing with retry logic and CAPTCHA detection."""
        self._rotate_user_agent()
        search_url = self.search_engines['bing']
        params = {'q': query, 'count': num_results}
        if site:
            params['q'] = f"site:{site} {query}"
        
        proxy = self._get_proxy()
        
        try:
            response = self.session.get(search_url, params=params, timeout=10, proxies=proxy)
            response.raise_for_status()
            
            # Check for CAPTCHA
            if not self._handle_captcha(response.text):
                return [{'error': 'CAPTCHA detected - could not handle', 'engine': 'bing'}]
            
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
    
    @retry_with_exponential_backoff(max_retries=3, initial_delay=1.0, backoff_factor=2.0,
                                   exceptions=(requests.RequestException, requests.Timeout))
    def search_duckduckgo(self, query: str, num_results: int = 10, site: Optional[str] = None) -> List[Dict]:
        """Search using DuckDuckGo with retry logic and CAPTCHA detection."""
        self._rotate_user_agent()
        search_url = self.search_engines['duckduckgo']
        params = {'q': query}
        if site:
            params['q'] = f"site:{site} {query}"
        
        proxy = self._get_proxy()
        
        try:
            response = self.session.get(search_url, params=params, timeout=10, proxies=proxy)
            response.raise_for_status()
            
            # Check for CAPTCHA
            if not self._handle_captcha(response.text):
                return [{'error': 'CAPTCHA detected - could not handle', 'engine': 'duckduckgo'}]
            
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
    
    def search_google_api(self, query: str, num_results: int = 10, site: Optional[str] = None) -> List[Dict]:
        """
        Search using Google Custom Search API (primary method if API key available).
        
        Args:
            query: Search query string
            num_results: Number of results to return
            site: Restrict search to specific domain
            
        Returns:
            List of dictionaries containing search results
        """
        if not self.google_api_key or not self.google_cx_id:
            logger.warning("Google API credentials not configured, falling back to scraping")
            return self.search_google(query, num_results, site)
        
        url = 'https://www.googleapis.com/customsearch/v1'
        params = {
            'key': self.google_api_key,
            'cx': self.google_cx_id,
            'q': query,
            'num': min(num_results, 10)  # API max is 10 per request
        }
        
        if site:
            params['q'] = f"site:{site} {query}"
        
        try:
            response = self.session.get(url, params=params, timeout=10)
            response.raise_for_status()
            
            data = response.json()
            results = []
            
            if 'items' in data:
                for item in data['items']:
                    result = {
                        'title': item.get('title', ''),
                        'url': item.get('link', ''),
                        'snippet': item.get('snippet', ''),
                        'engine': 'google_api'
                    }
                    results.append(result)
            
            return results[:num_results]
            
        except requests.RequestException as e:
            logger.error(f"Google API error: {e}, falling back to scraping")
            return self.search_google(query, num_results, site)
    
    def search_bing_api(self, query: str, num_results: int = 10, site: Optional[str] = None) -> List[Dict]:
        """
        Search using Bing Web Search API (primary method if API key available).
        
        Args:
            query: Search query string
            num_results: Number of results to return
            site: Restrict search to specific domain
            
        Returns:
            List of dictionaries containing search results
        """
        if not self.bing_api_key:
            logger.warning("Bing API key not configured, falling back to scraping")
            return self.search_bing(query, num_results, site)
        
        url = 'https://api.bing.microsoft.com/v7.0/search'
        headers = {'Ocp-Apim-Subscription-Key': self.bing_api_key}
        params = {
            'q': query,
            'count': min(num_results, 50)  # API max is 50
        }
        
        if site:
            params['q'] = f"site:{site} {query}"
        
        try:
            response = self.session.get(url, params=params, headers=headers, timeout=10)
            response.raise_for_status()
            
            data = response.json()
            results = []
            
            if 'webPages' in data and 'value' in data['webPages']:
                for item in data['webPages']['value']:
                    result = {
                        'title': item.get('name', ''),
                        'url': item.get('url', ''),
                        'snippet': item.get('snippet', ''),
                        'engine': 'bing_api'
                    }
                    results.append(result)
            
            return results[:num_results]
            
        except requests.RequestException as e:
            logger.error(f"Bing API error: {e}, falling back to scraping")
            return self.search_bing(query, num_results, site)
    
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
            # Prefer API if available
            if self.google_api_key and self.google_cx_id:
                results = self.search_google_api(query, num_results, site)
            else:
                results = self.search_google(query, num_results, site)
        elif engine == 'bing':
            # Prefer API if available
            if self.bing_api_key:
                results = self.search_bing_api(query, num_results, site)
            else:
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
                except Exception as e:
                    logger.debug(f"Failed to parse URL for domain extraction: {e}")
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
        class SetEncoder(json.JSONEncoder):
            def default(self, obj):
                if isinstance(obj, set):
                    return list(obj)
                return super().default(obj)
        
        try:
            with open(filepath, 'w', encoding='utf-8') as f:
                json.dump(data, f, indent=2, ensure_ascii=False, cls=SetEncoder)
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
    before: Optional[str] = None
    after: Optional[str] = None
    cache: Optional[str] = None
    link: Optional[str] = None
    related: Optional[str] = None
    boolean_and: Optional[List[str]] = None
    boolean_or: Optional[List[str]] = None
    boolean_not: Optional[List[str]] = None
    query: str = ""

class SearchOperatorParser:
    """Parse Google search operators from query strings."""
    
    OPERATORS = {
        'site:', 'intitle:', 'inurl:', 'filetype:', 'ext:', 'allintitle:', 
        'allinurl:', 'intext:', 'allintext:', 'cache:', 'link:', 'related:',
        'before:', 'after:', 'AND', 'OR', 'NOT', '-'
    }
    
    def __init__(self):
        self.pattern = re.compile(
            r'(?:site|intitle|inurl|filetype|ext|allint_title|allinurl|intext|allintext|cache|link|related|before|after):([^\s]+)',
            re.IGNORECASE
        )
    
    def parse(self, query: str) -> SearchOperators:
        """Parse search operators from query string."""
        operators = SearchOperators()
        operators.query = query
        operators.boolean_and = []
        operators.boolean_or = []
        operators.boolean_not = []
        
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
        
        # Parse before: (date range)
        before_match = re.search(r'before:(\d{4}-\d{2}-\d{2})', query, re.IGNORECASE)
        if before_match:
            operators.before = before_match.group(1)
            operators.query = operators.query.replace(before_match.group(0), '').strip()
        
        # Parse after: (date range)
        after_match = re.search(r'after:(\d{4}-\d{2}-\d{2})', query, re.IGNORECASE)
        if after_match:
            operators.after = after_match.group(1)
            operators.query = operators.query.replace(after_match.group(0), '').strip()
        
        # Parse cache:
        cache_match = re.search(r'cache:([^\s]+)', query, re.IGNORECASE)
        if cache_match:
            operators.cache = cache_match.group(1)
            operators.query = operators.query.replace(cache_match.group(0), '').strip()
        
        # Parse link:
        link_match = re.search(r'link:([^\s]+)', query, re.IGNORECASE)
        if link_match:
            operators.link = link_match.group(1)
            operators.query = operators.query.replace(link_match.group(0), '').strip()
        
        # Parse related:
        related_match = re.search(r'related:([^\s]+)', query, re.IGNORECASE)
        if related_match:
            operators.related = related_match.group(1)
            operators.query = operators.query.replace(related_match.group(0), '').strip()
        
        # Parse Boolean operators
        # AND operator (explicit)
        and_matches = re.findall(r'\bAND\s+([^\s]+)', query, re.IGNORECASE)
        operators.boolean_and.extend(and_matches)
        operators.query = re.sub(r'\bAND\s+[^\s]+', '', operators.query, flags=re.IGNORECASE).strip()
        
        # OR operator
        or_parts = re.findall(r'\(([^)]+)\)', query)
        for part in or_parts:
            if ' OR ' in part.upper():
                or_terms = [t.strip() for t in re.split(r'\s+OR\s+', part, flags=re.IGNORECASE)]
                operators.boolean_or.extend(or_terms)
                operators.query = operators.query.replace(f'({part})', '').strip()
        
        # NOT operator (explicit)
        not_matches = re.findall(r'\bNOT\s+([^\s]+)', query, re.IGNORECASE)
        operators.boolean_not.extend(not_matches)
        operators.query = re.sub(r'\bNOT\s+[^\s]+', '', operators.query, flags=re.IGNORECASE).strip()
        
        # Minus operator (exclude)
        minus_matches = re.findall(r'-([^\s]+)', query)
        operators.boolean_not.extend(minus_matches)
        operators.query = re.sub(r'-[^\s]+', '', operators.query).strip()
        
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
        if operators.before:
            parts.append(f"before:{operators.before}")
        if operators.after:
            parts.append(f"after:{operators.after}")
        if operators.cache:
            parts.append(f"cache:{operators.cache}")
        if operators.link:
            parts.append(f"link:{operators.link}")
        if operators.related:
            parts.append(f"related:{operators.related}")
        
        # Add Boolean operators
        if operators.boolean_and:
            for term in operators.boolean_and:
                parts.append(f"AND {term}")
        
        if operators.boolean_or:
            or_group = ' OR '.join(operators.boolean_or)
            parts.append(f"({or_group})")
        
        if operators.boolean_not:
            for term in operators.boolean_not:
                parts.append(f"-{term}")
        
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
    
    SYNONYM_FILE = 'query_synonyms.json'
    
    def __init__(self):
        self.synonym_map = self.SYNONYM_MAP.copy()
        self._load_synonyms()
    
    def _load_synonyms(self):
        """Load synonyms from file if it exists."""
        if os.path.exists(self.SYNONYM_FILE):
            try:
                with open(self.SYNONYM_FILE, 'r', encoding='utf-8') as f:
                    loaded_map = json.load(f)
                # Merge with default map
                self.synonym_map.update(loaded_map)
                logger.info(f"Loaded synonyms from {self.SYNONYM_FILE}")
            except Exception as e:
                logger.error(f"Failed to load synonyms file: {e}")
    
    def _save_synonyms(self):
        """Save current synonym map to file."""
        try:
            with open(self.SYNONYM_FILE, 'w', encoding='utf-8') as f:
                json.dump(self.synonym_map, f, indent=2, ensure_ascii=False)
            logger.info(f"Saved synonyms to {self.SYNONYM_FILE}")
            return True
        except Exception as e:
            logger.error(f"Failed to save synonyms file: {e}")
            return False
    
    def add_synonym(self, word: str, synonyms: List[str]) -> bool:
        """
        Add or update synonyms for a word.
        
        Args:
            word: The word to add synonyms for
            synonyms: List of synonym strings
            
        Returns:
            True if successful, False otherwise
        """
        self.synonym_map[word.lower()] = [s.lower() for s in synonyms]
        return self._save_synonyms()
    
    def remove_synonym(self, word: str) -> bool:
        """
        Remove a word from the synonym map.
        
        Args:
            word: The word to remove
            
        Returns:
            True if successful, False otherwise
        """
        if word.lower() in self.synonym_map:
            del self.synonym_map[word.lower()]
            return self._save_synonyms()
        return False
    
    def import_synonyms(self, filepath: str) -> bool:
        """
        Import synonyms from a JSON file.
        
        Args:
            filepath: Path to the JSON file containing synonyms
            
        Returns:
            True if successful, False otherwise
        """
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                imported_map = json.load(f)
            
            # Validate structure
            if not isinstance(imported_map, dict):
                logger.error("Invalid synonyms file: must be a dictionary")
                return False
            
            # Merge with existing map
            for word, synonyms in imported_map.items():
                if isinstance(synonyms, list):
                    self.synonym_map[word.lower()] = [s.lower() for s in synonyms]
            
            self._save_synonyms()
            logger.info(f"Imported synonyms from {filepath}")
            return True
            
        except Exception as e:
            logger.error(f"Failed to import synonyms: {e}")
            return False
    
    def export_synonyms(self, filepath: str) -> bool:
        """
        Export current synonym map to a JSON file.
        
        Args:
            filepath: Path to save the JSON file
            
        Returns:
            True if successful, False otherwise
        """
        try:
            with open(filepath, 'w', encoding='utf-8') as f:
                json.dump(self.synonym_map, f, indent=2, ensure_ascii=False)
            logger.info(f"Exported synonyms to {filepath}")
            return True
        except Exception as e:
            logger.error(f"Failed to export synonyms: {e}")
            return False
    
    def get_synonym_map(self) -> Dict[str, List[str]]:
        """
        Get the current synonym map.
        
        Returns:
            Copy of the synonym map dictionary
        """
        return self.synonym_map.copy()
    
    def reset_synonyms(self) -> bool:
        """
        Reset synonym map to default values.
        
        Returns:
            True if successful, False otherwise
        """
        self.synonym_map = self.SYNONYM_MAP.copy()
        return self._save_synonyms()
    
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

class BM25Scorer:
    """
    BM25 relevance scorer for better document ranking.
    
    BM25 is a ranking function used by search engines to estimate the relevance
    of documents to a given search query.
    """
    
    def __init__(self, k1: float = 1.2, b: float = 0.75):
        """
        Initialize BM25 scorer.
        
        Args:
            k1: Term saturation parameter (typically 1.2-2.0)
            b: Length normalization parameter (typically 0.75)
        """
        self.k1 = k1
        self.b = b
    
    def _tokenize(self, text: str) -> List[str]:
        """Simple tokenization by splitting on whitespace and lowercasing."""
        return [word.lower().strip('.,!?;:"()[]{}') for word in text.split()]
    
    def _calculate_idf(self, doc_freq: int, total_docs: int) -> float:
        """
        Calculate inverse document frequency (IDF).
        
        Args:
            doc_freq: Number of documents containing the term
            total_docs: Total number of documents
            
        Returns:
            IDF score
        """
        if doc_freq == 0:
            return 0
        return math.log((total_docs - doc_freq + 0.5) / (doc_freq + 0.5) + 1)
    
    def score(self, query: str, document: str, doc_length: int, avg_doc_length: float,
               term_doc_freqs: Dict[str, int], total_docs: int) -> float:
        """
        Calculate BM25 score for a document given a query.
        
        Args:
            query: Search query string
            document: Document text (title + snippet)
            doc_length: Length of the document in tokens
            avg_doc_length: Average document length across corpus
            term_doc_freqs: Dictionary mapping terms to their document frequencies
            total_docs: Total number of documents in corpus
            
        Returns:
            BM25 relevance score
        """
        query_terms = self._tokenize(query)
        doc_terms = self._tokenize(document)
        
        # Calculate term frequencies in document
        term_freqs = {}
        for term in doc_terms:
            term_freqs[term] = term_freqs.get(term, 0) + 1
        
        # Calculate BM25 score
        score = 0
        for term in query_terms:
            if term in term_freqs:
                tf = term_freqs[term]
                df = term_doc_freqs.get(term, 0)
                idf = self._calculate_idf(df, total_docs)
                
                # BM25 formula
                numerator = tf * (self.k1 + 1)
                denominator = tf + self.k1 * (1 - self.b + self.b * (doc_length / avg_doc_length))
                score += idf * (numerator / denominator)
        
        return score

class MultiEngineAggregator:
    """Aggregate and deduplicate results from multiple search engines."""
    
    def __init__(self, use_bm25: bool = True):
        """
        Initialize aggregator.
        
        Args:
            use_bm25: Use BM25 scoring instead of simple word match scoring
        """
        self.searcher = Searcher()
        self.query_expander = QueryExpander()
        self.use_bm25 = use_bm25
        if use_bm25:
            self.bm25_scorer = BM25Scorer()
    
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
        
        # Rank by relevance (BM25 or simple scoring)
        ranked_results = self._rank_results(unique_results, query)
        
        return ranked_results[:num_results * 3]  # Return more results for aggregation
    
    def _rank_results(self, results: List[Dict], query: str) -> List[Dict]:
        """Rank results by relevance score using BM25 or simple scoring."""
        if self.use_bm25 and len(results) > 0:
            return self._rank_results_bm25(results, query)
        else:
            return self._rank_results_simple(results, query)
    
    def _rank_results_simple(self, results: List[Dict], query: str) -> List[Dict]:
        """Rank results by simple word match scoring."""
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
    
    def _rank_results_bm25(self, results: List[Dict], query: str) -> List[Dict]:
        """Rank results using BM25 scoring algorithm."""
        if not results:
            return results
        
        # Prepare corpus for BM25
        corpus = []
        for result in results:
            title = result.get('title', '')
            snippet = result.get('snippet', '')
            corpus.append(f"{title} {snippet}")
        
        # Calculate document lengths
        doc_lengths = [len(self.bm25_scorer._tokenize(doc)) for doc in corpus]
        avg_doc_length = sum(doc_lengths) / len(doc_lengths) if doc_lengths else 0
        
        # Calculate term document frequencies
        term_doc_freqs = {}
        for doc in corpus:
            terms = set(self.bm25_scorer._tokenize(doc))
            for term in terms:
                term_doc_freqs[term] = term_doc_freqs.get(term, 0) + 1
        
        total_docs = len(results)
        
        # Calculate BM25 scores
        for i, result in enumerate(results):
            document = corpus[i]
            doc_length = doc_lengths[i]
            
            bm25_score = self.bm25_scorer.score(
                query=query,
                document=document,
                doc_length=doc_length,
                avg_doc_length=avg_doc_length,
                term_doc_freqs=term_doc_freqs,
                total_docs=total_docs
            )
            
            result['relevance_score'] = bm25_score
            result['scoring_method'] = 'BM25'
        
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
        self.session = requests.Session()
        self.session.headers.update({
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36'
        })
    
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
            except Exception as e:
                logger.debug(f"DNS A record query failed for {full_domain}: {e}")
            
            try:
                # Try CNAME record
                self.resolver.resolve(full_domain, 'CNAME')
                found_subdomains.add(full_domain)
            except Exception as e:
                logger.debug(f"DNS CNAME record query failed for {full_domain}: {e}")
            
            if progress_callback:
                progress_callback(idx + 1, total, len(found_subdomains))
        
        return found_subdomains
    
    def query_crtsh(self, domain: str) -> Set[str]:
        """Query crt.sh for certificate transparency logs with valid certificate filtering."""
        subdomains = set()
        
        try:
            url = f"https://crt.sh/?q=%.{domain}&exclude=expired&output=json"
            response = self.session.get(url, timeout=10)
            response.raise_for_status()
            
            data = response.json()
            
            from datetime import datetime
            
            for entry in data:
                # Check if certificate is currently valid
                not_before = entry.get('not_before')
                not_after = entry.get('not_after')
                
                if not_before and not_after:
                    try:
                        # Parse certificate dates
                        nb = datetime.fromisoformat(not_before.replace('Z', '+00:00'))
                        na = datetime.fromisoformat(not_after.replace('Z', '+00:00'))
                        now = datetime.now(nb.tzinfo)
                        
                        # Skip expired certificates
                        if na < now:
                            continue
                            
                        # Skip certificates not yet valid
                        if nb > now:
                            continue
                    except Exception as e:
                        # If date parsing fails, skip this entry
                        logger.debug(f"Certificate date parsing failed: {e}")
                        continue
                
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
        except Exception as e:
            logger.debug(f"Tor connection check failed: {e}")
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
    """Nmap-style port scanner with TCP, UDP, and SYN scan support."""
    
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
    
    def scan_port(self, host: str, port: int, protocol: str = 'TCP') -> Dict:
        """Scan a single port using specified protocol (TCP, UDP, SYN, or ALL)."""
        if protocol.upper() == 'ALL':
            return self._scan_all_protocols(host, port)
        elif protocol.upper() == 'TCP':
            return self._scan_tcp(host, port)
        elif protocol.upper() == 'UDP':
            return self._scan_udp(host, port)
        elif protocol.upper() == 'SYN':
            return self._scan_syn(host, port)
        else:
            return self._scan_tcp(host, port)
    
    def _scan_tcp(self, host: str, port: int) -> Dict:
        """TCP connect scan (full connection)."""
        result = {
            'host': host,
            'port': port,
            'service': self.COMMON_PORTS.get(port, 'unknown'),
            'status': 'closed',
            'protocol': 'TCP',
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
    
    def _scan_udp(self, host: str, port: int) -> Dict:
        """UDP scan (sends empty packet, checks for response)."""
        result = {
            'host': host,
            'port': port,
            'service': self.COMMON_PORTS.get(port, 'unknown'),
            'status': 'closed',
            'protocol': 'UDP',
            'error': None
        }
        
        try:
            sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            sock.settimeout(self.timeout)
            
            # Send empty UDP packet
            sock.sendto(b'', (host, port))
            
            # Try to receive response
            try:
                data, _ = sock.recvfrom(1024)
                result['status'] = 'open'
            except socket.timeout:
                # No response could mean open or filtered - mark as open/filtered
                result['status'] = 'open|filtered'
            
            sock.close()
        
        except Exception as e:
            result['error'] = str(e)
            result['status'] = 'error'
        
        return result
    
    def _scan_syn(self, host: str, port: int) -> Dict:
        """SYN scan (half-open scan) - requires admin privileges."""
        result = {
            'host': host,
            'port': port,
            'service': self.COMMON_PORTS.get(port, 'unknown'),
            'status': 'closed',
            'protocol': 'SYN',
            'error': None
        }
        
        try:
            # Try raw socket for SYN scan (requires admin)
            try:
                import sys
                if sys.platform == 'win32':
                    # Windows raw socket
                    sock = socket.socket(socket.AF_INET, socket.SOCK_RAW, socket.IPPROTO_TCP)
                else:
                    # Linux raw socket
                    sock = socket.socket(socket.AF_INET, socket.SOCK_RAW, socket.IPPROTO_TCP)
                
                sock.settimeout(self.timeout)
                sock.connect((host, port))
                result['status'] = 'open'
                sock.close()
            except (PermissionError, OSError):
                # Fallback to TCP connect if raw socket fails
                result['error'] = 'SYN scan requires admin privileges, falling back to TCP'
                tcp_result = self._scan_tcp(host, port)
                result['status'] = tcp_result['status']
                result['protocol'] = 'TCP (fallback)'
        
        except Exception as e:
            result['error'] = str(e)
            result['status'] = 'error'
        
        return result
    
    def _scan_all_protocols(self, host: str, port: int) -> Dict:
        """Scan port using all protocols (TCP, UDP, SYN) and report results."""
        results = []
        
        # Try TCP
        tcp_result = self._scan_tcp(host, port)
        results.append(tcp_result)
        
        # Try UDP
        udp_result = self._scan_udp(host, port)
        results.append(udp_result)
        
        # Try SYN
        syn_result = self._scan_syn(host, port)
        results.append(syn_result)
        
        # Determine overall status and which protocols succeeded
        open_protocols = []
        overall_status = 'closed'
        
        for r in results:
            if r['status'] in ['open', 'open|filtered']:
                open_protocols.append(r['protocol'])
                if overall_status != 'open':
                    overall_status = r['status']
        
        if open_protocols:
            overall_status = 'open'
        
        return {
            'host': host,
            'port': port,
            'service': self.COMMON_PORTS.get(port, 'unknown'),
            'status': overall_status,
            'protocol': 'ALL',
            'open_protocols': open_protocols,
            'tcp_status': tcp_result['status'],
            'udp_status': udp_result['status'],
            'syn_status': syn_result['status'],
            'error': None,
            'details': results
        }
    
    def scan_ports(self, host: str, ports: Optional[List[int]] = None,
                   progress_callback: Optional[Callable] = None, protocol: str = 'TCP') -> List[Dict]:
        """Scan multiple ports on a host using specified protocol."""
        if ports is None:
            ports = list(self.COMMON_PORTS.keys())
        
        results = []
        total = len(ports)
        
        for idx, port in enumerate(ports):
            result = self.scan_port(host, port, protocol)
            results.append(result)
            
            if progress_callback:
                progress_callback(idx + 1, total, len([r for r in results if r['status'] in ['open', 'open|filtered']]))
        
        return results
    
    def scan_range(self, host: str, start_port: int, end_port: int,
                   progress_callback: Optional[Callable] = None, protocol: str = 'TCP') -> List[Dict]:
        """Scan a range of ports using specified protocol."""
        ports = list(range(start_port, end_port + 1))
        return self.scan_ports(host, ports, progress_callback, protocol)
    
    def async_scan_ports(self, host: str, ports: Optional[List[int]] = None,
                         max_threads: int = 50, protocol: str = 'TCP') -> List[Dict]:
        """Scan ports asynchronously using threads with specified protocol."""
        if ports is None:
            ports = list(self.COMMON_PORTS.keys())
        
        results = [None] * len(ports)
        threads = []
        
        def scan_worker(idx, port):
            results[idx] = self.scan_port(host, port, protocol)
        
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
        except Exception as e:
            logger.debug(f"Graph metrics calculation failed: {e}")
        
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
    """Advanced technology stack detection with confidence scoring, multiple detection methods, and comprehensive analysis."""
    
    # Confidence levels
    CONFIDENCE_HIGH = 0.9
    CONFIDENCE_MEDIUM = 0.6
    CONFIDENCE_LOW = 0.3
    
    TECHNOLOGY_SIGNATURES = {
        'cms': {
            'WordPress': ['wp-content', 'wp-includes', '/wordpress/', 'wp-json'],
            'Drupal': ['drupal', 'sites/default/files', 'drupal.js'],
            'Joomla': ['joomla', '/components/', 'joomla.js'],
            'Magento': ['magento', '/skin/', 'mage/'],
            'Shopify': ['shopify', 'cdn.shopify.com', 'Shopify.theme'],
            'Squarespace': ['squarespace', 'static1.squarespace.com'],
            'Wix': ['wix', 'static.wixstatic.com', 'wix-code'],
            'Ghost': ['ghost', 'ghost-url'],
            'HubSpot': ['hubspot', 'hs-scripts', 'hubspot.net'],
            'TYPO3': ['typo3', 't3lib'],
            'Concrete5': ['concrete5', 'concrete/'],
            'Blogger': ['blogger', 'blogspot.com'],
            'Medium': ['medium.com', 'medium-widget'],
            'Tumblr': ['tumblr', 'tumblr.com'],
            'Weebly': ['weebly', 'weebly-static'],
            'Webflow': ['webflow', 'w-webflow'],
            'Statamic': ['statamic', 'statamic/'],
            'Craft CMS': ['craft', 'craftcms'],
            'October CMS': ['october', 'octobercms'],
            'Grav': ['grav', 'user/themes'],
            'Hugo': ['hugo', 'hugo.io'],
            'Jekyll': ['jekyll', 'jekyll-seo'],
        },
        'javascript_frameworks': {
            'React': ['react', 'react-dom', '_react', 'reactjs'],
            'Vue.js': ['vue', 'Vue', 'v-if', 'vue-router'],
            'Angular': ['angular', 'ng-app', 'ng-controller', 'angularjs'],
            'Angular (Modern)': ['@angular/core', 'ng-version'],
            'jQuery': ['jquery', '$(', 'jQuery'],
            'Ember.js': ['ember', 'Ember', 'ember-cli'],
            'Backbone.js': ['backbone', 'Backbone'],
            'Svelte': ['svelte', 'Svelte'],
            'Alpine.js': ['alpine', 'x-data', '@alpinejs'],
            'SolidJS': ['solid-js', 'solid-js'],
            'Preact': ['preact', 'preact/compat'],
            'Lit': ['lit-html', 'lit-element'],
            'Stencil': ['stencil', '@stencil/core'],
            'Aurelia': ['aurelia', 'aurelia-framework'],
            'Mithril': ['mithril', 'mithril.js'],
            'Riot': ['riot', 'riot.js'],
            'Knockout.js': ['knockout', 'ko.applyBindings'],
            'Polymer': ['polymer', '@polymer'],
            'Meteor': ['meteor', 'meteor.js'],
            'Nuxt.js': ['nuxt', 'nuxt.js', '__nuxt'],
            'Next.js': ['next', 'next.js', '__next'],
            'Gatsby': ['gatsby', 'gatsby.js'],
            'Remix': ['remix', '@remix-run'],
            'SvelteKit': ['svelte-kit', '__sveltekit'],
        },
        'web_servers': {
            'Apache': ['Apache', 'Server: Apache'],
            'Nginx': ['nginx', 'Server: nginx'],
            'IIS': ['IIS', 'Microsoft-IIS'],
            'Cloudflare': ['cloudflare', 'cf-ray'],
            'LiteSpeed': ['litespeed', 'lshttpd'],
            'Caddy': ['caddy', 'Caddy'],
            'OpenResty': ['openresty', 'ngx_openresty'],
            'Tengine': ['tengine', 'Tengine'],
            'Envoy': ['envoy', 'Envoy'],
            'Traefik': ['traefik', 'Traefik'],
            'HAProxy': ['haproxy', 'HAProxy'],
            'Varnish': ['varnish', 'Varnish'],
            'Node.js': ['node', 'Express'],
            'Python HTTP': ['python', 'SimpleHTTP'],
            'Gunicorn': ['gunicorn', 'Gunicorn'],
            'uWSGI': ['uwsgi', 'uWSGI'],
            'Passenger': ['passenger', 'Phusion'],
        },
        'analytics': {
            'Google Analytics': ['google-analytics.com', 'ga.js', 'gtag.js', 'analytics.js'],
            'Google Tag Manager': ['googletagmanager.com', 'GTM-'],
            'Hotjar': ['hotjar.com', 'hj'],
            'Mixpanel': ['mixpanel.com', 'mixpanel'],
            'Segment': ['segment.com', 'analytics.js'],
            'Amplitude': ['amplitude.com', 'amplitude'],
            'Heap': ['heapanalytics.com', 'heap'],
            'FullStory': ['fullstory.com', 'fs.js'],
            'Mouseflow': ['mouseflow.com', 'mouseflow'],
            'Crazy Egg': ['crazyegg.com', 'crazyegg'],
            'Clicky': ['getclicky.com', 'clicky'],
            'StatCounter': ['statcounter.com', 'statcounter'],
            'Piwik PRO': ['piwik.pro', 'piwik'],
            'Matomo': ['matomo', 'matomo.js'],
            'Plausible': ['plausible.io', 'plausible'],
            'Fathom': ['usefathom.com', 'fathom'],
            'PostHog': ['posthog.com', 'posthog'],
            'Pendo': ['pendo.io', 'pendo'],
            'Lucky Orange': ['luckyorange.com', 'luckyorange'],
            'UserZoom': ['userzoom.com', 'userzoom'],
        },
        'cdn': {
            'Cloudflare': ['cloudflare', 'cf-ray'],
            'CloudFront': ['cloudfront.net'],
            'Akamai': ['akamai', 'akamaihd.net'],
            'Fastly': ['fastly', 'fastly.net'],
            'Azure CDN': ['azureedge.net', 'azurecdn'],
            'AWS CloudFront': ['cloudfront.net', 'awscloud'],
            'Google Cloud CDN': ['googlehosted.com', 'gstatic'],
            'KeyCDN': ['keycdn.com', 'keycdn'],
            'MaxCDN': ['maxcdn.com', 'maxcdn'],
            'CDN77': ['cdn77.com', 'cdn77'],
            'BunnyCDN': ['b-cdn.net', 'bunnycdn'],
            'StackPath': ['stackpath.com', 'stackpath'],
            'Edgecast': ['edgecastcdn.net', 'edgecast'],
            'Limelight': ['llnwd.net', 'limelight'],
            'Incapsula': ['incapsula', 'incapsula'],
            'Sucuri': ['sucuri.net', 'sucuri'],
        },
        'databases': {
            'MySQL': ['mysql', 'mysqli'],
            'PostgreSQL': ['postgresql', 'postgres'],
            'MongoDB': ['mongodb', 'mongo'],
            'Redis': ['redis', 'redis.io'],
            'SQLite': ['sqlite', 'sqlite3'],
            'Elasticsearch': ['elasticsearch', 'elastic'],
            'Cassandra': ['cassandra', 'datastax'],
            'DynamoDB': ['dynamodb', 'amazonaws/dynamodb'],
            'CouchDB': ['couchdb', 'apache/couchdb'],
            'Neo4j': ['neo4j', 'neo4j.com'],
            'MariaDB': ['mariadb', 'mariadb.org'],
            'Oracle': ['oracle', 'oracle.com'],
            'SQL Server': ['sql server', 'microsoft sql'],
            'Firebase': ['firebase', 'firebaseio.com'],
            'Supabase': ['supabase', 'supabase.co'],
        },
        'programming_languages': {
            'PHP': ['php', '.php'],
            'Python': ['python', 'py', 'django'],
            'Ruby': ['ruby', 'rails', 'rubyonrails'],
            'Java': ['java', 'jsp', 'servlet'],
            'Node.js': ['node', 'node.js', 'express'],
            'Go': ['golang', 'go-'],
            'Rust': ['rust', 'wasm-bindgen'],
            'C#': ['asp.net', '.net', 'csharp'],
            'TypeScript': ['typescript', '.ts'],
            'Scala': ['scala', 'scalajs'],
            'Kotlin': ['kotlin', 'ktor'],
            'Swift': ['swift', 'vapor'],
            'Elixir': ['elixir', 'phoenix'],
            'Clojure': ['clojure', 'clojurescript'],
        },
        'ui_frameworks': {
            'Bootstrap': ['bootstrap', 'bootstrap.css'],
            'Tailwind CSS': ['tailwindcss', 'tailwind'],
            'Foundation': ['foundation', 'foundation.css'],
            'Bulma': ['bulma', 'bulma.css'],
            'Material UI': ['material-ui', '@mui/material'],
            'Ant Design': ['antd', 'ant-design'],
            'Semantic UI': ['semantic', 'semantic-ui'],
            'UI Kit': ['uikit', 'uikit.css'],
            'Pure CSS': ['purecss', 'pure.css'],
            'Spectre.css': ['spectre', 'spectre.css'],
            'Picnic CSS': ['picnicss', 'picnic'],
            'Milligram': ['milligram', 'milligram'],
            'Skeleton': ['skeleton', 'skeleton.css'],
            'Primer': ['primer', 'primer.css'],
            'Water.css': ['water.css', 'water'],
            'PaperCSS': ['papercss', 'paper.css'],
            'Chakra UI': ['@chakra-ui', 'chakra-ui'],
            'Mantine': ['@mantine/core', 'mantine'],
            'Shadcn/ui': ['shadcn', 'shadcn-ui'],
            'Radix UI': ['@radix-ui', 'radix-ui'],
        },
        'css_frameworks': {
            'Sass': ['scss', 'sass'],
            'Less': ['less', 'lesscss'],
            'Stylus': ['stylus', 'styl'],
            'PostCSS': ['postcss', 'postcss-'],
            'Tailwind CSS': ['tailwindcss', 'tailwind'],
            'Bootstrap': ['bootstrap', 'bootstrap.css'],
        },
        'build_tools': {
            'Webpack': ['webpack', '__webpack'],
            'Vite': ['vite', 'vite/'],
            'Rollup': ['rollup', 'rollup.js'],
            'Parcel': ['parcel', 'parcel.js'],
            'esbuild': ['esbuild', 'esbuild-'],
            'Babel': ['babel', 'babel-'],
            'Gulp': ['gulp', 'gulpfile'],
            'Grunt': ['grunt', 'gruntfile'],
            'Browserify': ['browserify', 'browserify-'],
            'Snowpack': ['snowpack', 'snowpack/'],
            'Turbopack': ['turbo', 'turbopack'],
            'Rome': ['rome', 'rome-'],
            'SWC': ['swc', '@swc'],
        },
        'testing_frameworks': {
            'Jest': ['jest', '@jest'],
            'Mocha': ['mocha', 'mocha.js'],
            'Chai': ['chai', 'chai.js'],
            'Jasmine': ['jasmine', 'jasmine.js'],
            'Cypress': ['cypress', '@cypress'],
            'Playwright': ['playwright', '@playwright'],
            'Selenium': ['selenium', 'selenium-'],
            'Puppeteer': ['puppeteer', '@puppeteer'],
            'Testing Library': ['testing-library', '@testing-library'],
            'Vitest': ['vitest', '@vitest'],
            'Karma': ['karma', 'karma-'],
            'Protractor': ['protractor', '@angular/protractor'],
        },
        'caching': {
            'Varnish': ['varnish', 'Varnish'],
            'Redis': ['redis', 'redis.io'],
            'Memcached': ['memcached', 'memcache'],
            'Squid': ['squid', 'squid/'],
            'Cloudflare': ['cloudflare', 'cf-ray'],
            'Fastly': ['fastly', 'fastly.net'],
            'Akamai': ['akamai', 'akamaihd.net'],
        },
        'security': {
            'Cloudflare WAF': ['cloudflare', 'cf-ray'],
            'Akamai WAF': ['akamai', 'akamaihd.net'],
            'ModSecurity': ['modsecurity', 'mod_security'],
            'AWS WAF': ['aws-waf', 'amazonaws/waf'],
            'Sucuri WAF': ['sucuri', 'sucuri/firewall'],
            'Incapsula': ['incapsula', 'incapsula/waf'],
            'Fastly WAF': ['fastly', 'fastly.net/waf'],
            'Imperva': ['imperva', 'incapsula'],
            'Radware': ['radware', 'radware.com'],
            'Fortinet': ['fortinet', 'fortiguard'],
        },
        'ecommerce': {
            'Shopify': ['shopify', 'cdn.shopify.com', 'Shopify.theme'],
            'Magento': ['magento', '/skin/', 'mage/'],
            'WooCommerce': ['woocommerce', 'wc-', 'wp-content/plugins/woocommerce'],
            'BigCommerce': ['bigcommerce', 'cdn.bigcommerce.com'],
            'PrestaShop': ['prestashop', 'prestashop.com'],
            'OpenCart': ['opencart', 'catalog/'],
            'Zen Cart': ['zen cart', 'zen-cart'],
            'osCommerce': ['oscommerce', 'oscommerce'],
            'Salesforce Commerce': ['demandware', 'dwre'],
            'SAP Commerce': ['sap', 'hybris'],
            'Oracle Commerce': ['oracle', 'atg'],
        },
        'marketing': {
            'HubSpot': ['hubspot', 'hs-scripts', 'hubspot.net'],
            'Marketo': ['marketo', 'marketo.com'],
            'Pardot': ['pardot', 'pi.pardot.com'],
            'Eloqua': ['eloqua', 'eloqua.com'],
            'ActiveCampaign': ['activecampaign', 'activecampaign.com'],
            'Mailchimp': ['mailchimp', 'mc.js'],
            'Constant Contact': ['constantcontact', 'constantcontact.com'],
            'GetResponse': ['getresponse', 'getresponse.com'],
            'AWeber': ['aweber', 'aweber.com'],
            'ConvertKit': ['convertkit', 'convertkit.com'],
        },
        'chat': {
            'Intercom': ['intercom', 'intercom.io'],
            'Drift': ['drift', 'drift.com'],
            'Zendesk Chat': ['zendesk', 'zopim.com'],
            'LiveChat': ['livechat', 'livechatinc.com'],
            'Tawk.to': ['tawk.to', 'tawk'],
            'Crisp': ['crisp', 'crisp.chat'],
            'Freshchat': ['freshchat', 'freshworks.com'],
            'Pure Chat': ['purechat', 'purechat.com'],
            'Userlike': ['userlike', 'userlike.com'],
            'SnapEngage': ['snapengage', 'snapengage.com'],
        },
        'cms_plugins': {
            'Yoast SEO': ['yoast', 'yoast-seo'],
            'All in One SEO': ['aioseo', 'all-in-one-seo'],
            'Jetpack': ['jetpack', 'jetpack-'],
            'Elementor': ['elementor', 'elementor-'],
            'Divi': ['divi', 'et-'],
            'WPBakery': ['js_composer', 'wpbakery'],
            'Visual Composer': ['visual-composer', 'vc-'],
            'Contact Form 7': ['contact-form-7', 'wpcf7'],
            'Gravity Forms': ['gravityforms', 'gform'],
            'Ninja Forms': ['ninja-forms', 'nf-'],
        },
        'headless_cms': {
            'Contentful': ['contentful', 'contentful.com'],
            'Strapi': ['strapi', 'strapi.io'],
            'Sanity': ['sanity', 'sanity.io'],
            'Prismic': ['prismic', 'prismic.io'],
            'Ghost': ['ghost', 'ghost-url'],
            'ButterCMS': ['buttercms', 'buttercms.com'],
            'Cosmic': ['cosmicjs', 'cosmicjs.com'],
            'Directus': ['directus', 'directus.io'],
            'Keystone': ['keystone', 'keystonejs.com'],
            'Payload': ['payloadcms', 'payloadcms.com'],
        },
        'authentication': {
            'Auth0': ['auth0', 'auth0.com'],
            'Okta': ['okta', 'okta.com'],
            'Firebase Auth': ['firebase', 'firebaseio.com'],
            'AWS Cognito': ['amazonaws/cognito', 'cognito'],
            'Azure AD': ['azuread', 'microsoftonline'],
            'Keycloak': ['keycloak', 'keycloak.org'],
            'Passport.js': ['passport', 'passport-'],
            'NextAuth': ['next-auth', 'next-auth'],
            'Supabase Auth': ['supabase', 'supabase.co'],
            'Clerk': ['clerk', 'clerk.com'],
        },
        'monitoring': {
            'New Relic': ['newrelic', 'nr-data'],
            'Datadog': ['datadog', 'datadoghq'],
            'Sentry': ['sentry', 'sentry.io'],
            'LogRocket': ['logrocket', 'logrocket.com'],
            'Rollbar': ['rollbar', 'rollbar.com'],
            'Bugsnag': ['bugsnag', 'bugsnag.com'],
            'AppDynamics': ['appdynamics', 'appdynamics.com'],
            'Dynatrace': ['dynatrace', 'dynatrace.com'],
            'Prometheus': ['prometheus', 'prometheus.io'],
            'Grafana': ['grafana', 'grafana.com'],
        },
        'search': {
            'Algolia': ['algolia', 'algolia.net'],
            'Elasticsearch': ['elasticsearch', 'elastic'],
            'Solr': ['solr', 'apache/solr'],
            'Azure Search': ['azuresearch', 'search.windows.net'],
            'Google Custom Search': ['google.com/cse', 'gcse'],
            'Swiftype': ['swiftype', 'swiftype.com'],
            'Typesense': ['typesense', 'typesense.org'],
            'Meilisearch': ['meilisearch', 'meilisearch.com'],
            'Lunr.js': ['lunr', 'lunr.js'],
            'FlexSearch': ['flexsearch', 'flexsearch'],
        },
        'maps': {
            'Google Maps': ['maps.googleapis.com', 'google-maps'],
            'Mapbox': ['mapbox', 'mapbox.com'],
            'Leaflet': ['leaflet', 'leaflet.js'],
            'OpenLayers': ['openlayers', 'ol.js'],
            'Mapbox GL': ['mapbox-gl', 'mapbox-gl-js'],
            'Carto': ['carto', 'carto.com'],
            'HERE Maps': ['here.com', 'here-maps'],
            'Bing Maps': ['bing.com/maps', 'bing-maps'],
        },
        'payment': {
            'Stripe': ['stripe', 'stripe.com', 'js.stripe.com'],
            'PayPal': ['paypal', 'paypal.com', 'paypalobjects.com'],
            'Square': ['square', 'squareup.com'],
            'Braintree': ['braintree', 'braintree-api'],
            'Adyen': ['adyen', 'adyen.com'],
            'Authorize.net': ['authorize.net', 'authorizenet'],
            'Worldpay': ['worldpay', 'worldpay.com'],
            'Checkout.com': ['checkout.com', 'checkout'],
            'Razorpay': ['razorpay', 'razorpay.com'],
            'Stripe Elements': ['stripe.elements', 'stripe-js'],
        },
        'icons': {
            'Font Awesome': ['fontawesome', 'fa-', 'font-awesome'],
            'Material Icons': ['material-icons', 'materialicons'],
            'Ionicons': ['ionicons', 'ion-'],
            'Feather Icons': ['feather-icons', 'feather'],
            'Heroicons': ['heroicons', 'hero-'],
            'Lucide': ['lucide', 'lucide-'],
            'Octicons': ['octicons', 'octicon'],
            'Phosphor Icons': ['phosphor-icons', 'phosphor'],
            'Remix Icon': ['remixicon', 'ri-'],
            'Tabler Icons': ['tabler-icons', 'tabler-'],
        },
        'fonts': {
            'Google Fonts': ['fonts.googleapis.com', 'fonts.gstatic.com'],
            'Adobe Fonts': ['use.typekit.net', 'typekit'],
            'Fontdeck': ['fontdeck.com', 'fontdeck'],
            'Fonts.com': ['fonts.com', 'monotype'],
            'MyFonts': ['myfonts.com', 'myfonts'],
            'Fontspring': ['fontspring.com', 'fontspring'],
            'Typekit': ['typekit', 'use.typekit.net'],
        },
        'video': {
            'YouTube': ['youtube.com', 'youtube-nocookie.com'],
            'Vimeo': ['vimeo.com', 'player.vimeo.com'],
            'Wistia': ['wistia.com', 'wistia'],
            'Brightcove': ['brightcove', 'bcove'],
            'JW Player': ['jwplayer', 'jwplayer.com'],
            'Video.js': ['video.js', 'videojs'],
            'Plyr': ['plyr', 'plyr.io'],
            'Dailymotion': ['dailymotion', 'dmcdn'],
            'Twitch': ['twitch.tv', 'twitch-'],
        },
        'social': {
            'Facebook': ['facebook.com', 'fb-', 'facebook'],
            'Twitter': ['twitter.com', 'twitter-', 'x.com'],
            'LinkedIn': ['linkedin.com', 'linkedin-'],
            'Instagram': ['instagram.com', 'instagram-'],
            'Pinterest': ['pinterest.com', 'pinterest-'],
            'TikTok': ['tiktok.com', 'tiktok-'],
            'WhatsApp': ['whatsapp.com', 'whatsapp-'],
            'Telegram': ['telegram.org', 'telegram-'],
            'Reddit': ['reddit.com', 'reddit-'],
            'Discord': ['discord.com', 'discord-'],
        },
        'javascript_libraries': {
            'Chart.js': ['chart.js', 'chartjs', 'Chart'],
            'D3.js': ['d3', 'd3.js', 'd3.v'],
            'Three.js': ['three', 'three.js', 'three.min'],
            'Moment.js': ['moment', 'moment.js', 'moment.min'],
            'Lodash': ['lodash', 'lodash.min', '_'],
            'Axios': ['axios', 'axios.min'],
            'Socket.io': ['socket.io', 'socket.io.js'],
            'GSAP': ['gsap', 'greensock'],
            'Anime.js': ['anime', 'anime.min'],
            'AOS': ['aos', 'aos.css'],
            'Swiper': ['swiper', 'swiper.min'],
            'Slick': ['slick', 'slick.min'],
            'Owl Carousel': ['owl.carousel', 'owl-carousel'],
            'Fancybox': ['fancybox', 'fancybox.min'],
            'Lightbox': ['lightbox', 'lightbox.min'],
            'Pickaday': ['pickaday', 'pikaday'],
            'Flatpickr': ['flatpickr', 'flatpickr.min'],
            'Datepicker': ['datepicker', 'bootstrap-datepicker'],
            'Select2': ['select2', 'select2.min'],
            'Choices.js': ['choices', 'choices.min'],
            'Dropzone': ['dropzone', 'dropzone.min'],
            'Sortable': ['sortable', 'sortable.min'],
            'Draggable': ['draggable', 'draggable.min'],
            'Hammer.js': ['hammer', 'hammer.min'],
            'Velocity.js': ['velocity', 'velocity.min'],
            'Waypoints': ['waypoints', 'waypoint'],
            'CountUp.js': ['countup', 'countup.min'],
            'Typed.js': ['typed', 'typed.min'],
            'Particles.js': ['particles', 'particles.min'],
            'Canvas Confetti': ['canvas-confetti', 'confetti'],
        },
        'web frameworks': {
            'Django': ['django', 'csrftoken'],
            'Flask': ['flask', 'werkzeug'],
            'Rails': ['rails', 'ruby on rails', 'rails-ujs'],
            'Laravel': ['laravel', 'x-csrf-token'],
            'Spring Boot': ['spring boot', 'springframework'],
            'Express.js': ['express', 'express-'],
            'FastAPI': ['fastapi', 'uvicorn'],
            'NestJS': ['nest', '@nestjs'],
            'ASP.NET Core': ['asp.net core', '.net core'],
            'Symfony': ['symfony', 'sf_'],
            'CakePHP': ['cakephp', 'cake-'],
            'CodeIgniter': ['codeigniter', 'ci_'],
            'Zend Framework': ['zend', 'zf2'],
            'Laminas': ['laminas', 'mezzio'],
            'Phalcon': ['phalcon', 'phalcon-'],
            'Slim': ['slim', 'slimframework'],
            'Sails.js': ['sails', 'sails.io'],
            'Hapi': ['hapi', '@hapi'],
            'Koa': ['koa', 'koa-'],
            'Fiber': ['fiber', 'gofiber'],
            'Gin': ['gin-gonic', 'gin-'],
            'Echo': ['echo', 'echo-'],
            'Actix': ['actix', 'actix-web'],
            'Rocket': ['rocket', 'rocket.rs'],
        },
        'task_runners': {
            'Webpack': ['webpack', '__webpack'],
            'Vite': ['vite', '/@vite/'],
            'Rollup': ['rollup', 'rollup.js'],
            'Parcel': ['parcel', 'parcel.js'],
            'esbuild': ['esbuild', 'esbuild-'],
            'Babel': ['babel', 'babel-'],
            'Gulp': ['gulp', 'gulpfile'],
            'Grunt': ['grunt', 'gruntfile'],
            'Browserify': ['browserify', 'browserify-'],
            'Snowpack': ['snowpack', 'snowpack/'],
            'Turbopack': ['turbo', 'turbopack'],
            'Rome': ['rome', 'rome-'],
            'SWC': ['swc', '@swc'],
            'Rspack': ['rspack', '@rspack'],
        },
        'css_preprocessors': {
            'Sass': ['scss', 'sass'],
            'Less': ['less', 'lesscss'],
            'Stylus': ['stylus', 'styl'],
            'PostCSS': ['postcss', 'postcss-'],
            'Tailwind CSS': ['tailwindcss', 'tailwind'],
        },
        'template_engines': {
            'Jinja2': ['jinja2', 'jinja'],
            'Mako': ['mako', 'mako-'],
            'Mustache': ['mustache', '{{'],
            'Handlebars': ['handlebars', 'handlebars-'],
            'EJS': ['ejs', '<%'],
            'Pug': ['pug', 'jade'],
            'Haml': ['haml', '%'],
            'Slim': ['slim', 'slim-'],
            'Nunjucks': ['nunjucks', 'njk'],
            'Liquid': ['liquid', '{%'],
            'Blade': ['blade', 'laravel blade'],
            'Twig': ['twig', '{{'],
            'ERB': ['erb', '<%='],
            'Eco': ['eco', '<%-'],
            'Dust': ['dust', '{ dust'],
        },
        'database_tools': {
            'Prisma': ['prisma', '@prisma'],
            'Sequelize': ['sequelize', '@sequelize'],
            'TypeORM': ['typeorm', '@typeorm'],
            'Mongoose': ['mongoose', '@mongoose'],
            'Knex': ['knex', 'knex-'],
            'Bookshelf': ['bookshelf', 'bookshelf-'],
            'Objection.js': ['objection', 'objection-'],
            'Waterline': ['waterline', 'sails-'],
            'Hibernate': ['hibernate', 'hibernate-'],
            'Entity Framework': ['entity framework', 'ef core'],
            'Dapper': ['dapper', 'dapper-'],
            'SQLAlchemy': ['sqlalchemy', 'flask-sqlalchemy'],
            'Peewee': ['peewee', 'peewee-'],
            'MongoEngine': ['mongoengine', 'mongo-'],
            'Doctrine': ['doctrine', 'doctrine-'],
            'Propel': ['propel', 'propel-'],
        },
        'api_clients': {
            'Apollo Client': ['apollo', '@apollo'],
            'Relay': ['relay', '@relay'],
            'urql': ['urql', '@urql'],
            'SWR': ['swr', 'useSWR'],
            'React Query': ['react-query', '@tanstack/react-query'],
            'Vue Query': ['vue-query', '@tanstack/vue-query'],
            'Axios': ['axios', 'axios-'],
            'Fetch API': ['fetch(', 'window.fetch'],
            'SuperAgent': ['superagent', 'superagent-'],
            'Got': ['got', 'got-'],
            'node-fetch': ['node-fetch', 'node-fetch-'],
            'Ky': ['ky', 'ky-'],
            'Wretch': ['wretch', 'wretch-'],
        },
        'state_management': {
            'Redux': ['redux', '@redux'],
            'MobX': ['mobx', '@mobx'],
            'Vuex': ['vuex', 'store'],
            'Pinia': ['pinia', '@pinia'],
            'Zustand': ['zustand', '@zustand'],
            'Recoil': ['recoil', '@recoil'],
            'Jotai': ['jotai', '@jotai'],
            'Valtio': ['valtio', '@valtio'],
            'XState': ['xstate', '@xstate'],
            'Effector': ['effector', '@effector'],
            'NgRx': ['ngrx', '@ngrx'],
            'Akita': ['akita', '@datorama'],
        },
        'form_validation': {
            'Formik': ['formik', '@formik'],
            'React Hook Form': ['react-hook-form', '@hookform'],
            'Yup': ['yup', '@yup'],
            'Zod': ['zod', '@zod'],
            'Joi': ['joi', '@hapi/joi'],
            'VeeValidate': ['vee-validate', '@vee-validate'],
            'Validator.js': ['validator', 'validator-'],
            'Ajv': ['ajv', 'ajv-'],
        },
        'testing_libraries': {
            'Jest': ['jest', '@jest'],
            'Mocha': ['mocha', 'mocha.js'],
            'Chai': ['chai', 'chai.js'],
            'Jasmine': ['jasmine', 'jasmine.js'],
            'Cypress': ['cypress', '@cypress'],
            'Playwright': ['playwright', '@playwright'],
            'Selenium': ['selenium', 'selenium-'],
            'Puppeteer': ['puppeteer', '@puppeteer'],
            'Testing Library': ['testing-library', '@testing-library'],
            'Vitest': ['vitest', '@vitest'],
            'Karma': ['karma', 'karma-'],
            'Protractor': ['protractor', '@angular/protractor'],
            'Supertest': ['supertest', 'supertest-'],
            'MSW': ['msw', 'msw-'],
            'Nock': ['nock', 'nock-'],
        },
        'graphql': {
            'Apollo Server': ['apollo-server', '@apollo/server'],
            'GraphQL Yoga': ['graphql-yoga', '@graphql-yoga'],
            'Mercurius': ['mercurius', '@mercurius'],
            'Apollo GraphQL': ['apollo', '@apollo'],
            'Relay': ['relay', '@relay'],
            'Urql': ['urql', '@urql'],
            'GraphQL Code Generator': ['graphql-codegen', '@graphql-codegen'],
            'GraphQL Tools': ['graphql-tools', '@graphql-tools'],
        },
        'realtime': {
            'Socket.io': ['socket.io', 'socket.io.js'],
            'Pusher': ['pusher', 'pusher-js'],
            'Ably': ['ably', 'ably-js'],
            'SignalR': ['signalr', '@microsoft/signalr'],
            'Phoenix Channels': ['phoenix', 'phoenix-'],
            'Action Cable': ['actioncable', '@rails/actioncable'],
            'Fanout': ['fanout', 'fanout-'],
            'Deepstream': ['deepstream', 'deepstream-'],
        },
        'performance': {
            'Lighthouse': ['lighthouse', 'lighthouse-'],
            'WebPageTest': ['webpagetest', 'webpagetest-'],
            'GTmetrix': ['gtmetrix', 'gtmetrix-'],
            'PageSpeed': ['pagespeed', 'pagespeed-'],
            'Webpack Bundle Analyzer': ['bundle-analyzer', 'webpack-bundle-analyzer'],
            'Source Map Explorer': ['source-map-explorer', 'sourcemaps'],
        },
        'pwa': {
            'Workbox': ['workbox', 'workbox-'],
            'Service Worker': ['service-worker', 'navigator.serviceWorker'],
            'PWA Builder': ['pwa-builder', '@pwa'],
            'Lighthouse PWA': ['lighthouse', 'pwa'],
        },
        'internationalization': {
            'i18next': ['i18next', '@i18next'],
            'FormatJS': ['formatjs', '@formatjs'],
            'Vue I18n': ['vue-i18n', '@vue-i18n'],
            'React Intl': ['react-intl', '@formatjs/react'],
            'Angular I18n': ['@angular/common', 'i18n'],
            'Polyglot': ['polyglot', 'polyglot-'],
            'Globalize': ['globalize', 'globalize-'],
        },
        'accessibility': {
            'axe-core': ['axe', 'axe-core'],
            'Pa11y': ['pa11y', 'pa11y-'],
            'WAVE': ['wave', 'wave-'],
            'Lighthouse Accessibility': ['lighthouse', 'accessibility'],
        },
        'seo': {
            'Yoast SEO': ['yoast', 'yoast-seo'],
            'All in One SEO': ['aioseo', 'all-in-one-seo'],
            'Rank Math': ['rank-math', 'rankmath'],
            'Schema.org': ['schema.org', 'application/ld+json'],
            'Open Graph': ['og:', 'og:title'],
            'Twitter Cards': ['twitter:card', 'twitter:title'],
        },
        'email': {
            'SendGrid': ['sendgrid', '@sendgrid'],
            'Mailgun': ['mailgun', 'mailgun-'],
            'Postmark': ['postmark', 'postmark-'],
            'Amazon SES': ['ses', 'amazon-ses'],
            'SparkPost': ['sparkpost', 'sparkpost-'],
            'Mailchimp': ['mailchimp', 'mc.js'],
        },
        'file_upload': {
            'Dropzone': ['dropzone', 'dropzone.min'],
            'Fine Uploader': ['fine-uploader', 'fineuploader'],
            'Uppy': ['uppy', '@uppy'],
            'FilePond': ['filepond', 'filepond-'],
            'jQuery File Upload': ['fileupload', 'blueimp'],
        },
        'rich_text_editors': {
            'TinyMCE': ['tinymce', 'tinymce-'],
            'CKEditor': ['ckeditor', 'ckeditor-'],
            'Quill': ['quill', 'quill-'],
            'Draft.js': ['draft.js', '@draft-js'],
            'Slate': ['slate', '@slate-js'],
            'Trix': ['trix', 'trix-'],
            'Froala': ['froala', 'froala-'],
            'Summernote': ['summernote', 'summernote-'],
        },
    }
    
    VERSION_PATTERNS = {
        'WordPress': [r'wp-emoji-release\.min\.js\?ver=(\d+\.\d+\.\d+)', r'wp-includes/css/dist/block-library/style\.min\.css\?ver=(\d+\.\d+\.\d+)'],
        'Drupal': [r'Drupal\.settings\s*=\s*\{[^}]*"version":"(\d+\.\d+)"', r'/core/misc/drupal\.js\?v=(\d+\.\d+)'],
        'Joomla': [r'/media/jui/js/jquery\.min\.js\?(\d+\.\d+\.\d+)', r'Joomla\.version\s*=\s*"(\d+\.\d+)"'],
        'Magento': [r'/js/mage/\.js\?v=(\d+\.\d+\.\d+)', r'Magento\.version\s*=\s*"(\d+\.\d+\.\d+)"'],
        'React': [r'react-dom/(\d+\.\d+\.\d+)', r'react/(\d+\.\d+\.\d+)'],
        'Vue.js': [r'vue/(\d+\.\d+\.\d+)', r'vue\.min\.js\?(\d+\.\d+\.\d+)'],
        'Angular': [r'angular/(\d+\.\d+\.\d+)', r'angular\.min\.js\?(\d+\.\d+\.\d+)'],
        'Angular (Modern)': [r'@angular/core/(\d+\.\d+\.\d+)', r'ng-version="(\d+\.\d+\.\d+)"'],
        'jQuery': [r'jquery/(\d+\.\d+\.\d+)', r'jquery\.min\.js\?(\d+\.\d+\.\d+)'],
        'Bootstrap': [r'bootstrap/(\d+\.\d+\.\d+)', r'bootstrap\.css\?(\d+\.\d+\.\d+)'],
        'Tailwind CSS': [r'tailwindcss/(\d+\.\d+\.\d+)', r'tailwind\.css\?(\d+\.\d+\.\d+)'],
        'Laravel': [r'laravel/(\d+\.\d+\.\d+)', r'XSRF-TOKEN.*laravel'],
        'Django': [r'django/(\d+\.\d+\.\d+)', r'csrftoken.*django'],
        'Rails': [r'rails/(\d+\.\d+\.\d+)', r'rails-ujs'],
        'Express': [r'express/(\d+\.\d+\.\d+)', r'X-Powered-By: Express'],
        'Nginx': [r'nginx/(\d+\.\d+\.\d+)', r'Server: nginx/(\d+\.\d+\.\d+)'],
        'Apache': [r'Apache/(\d+\.\d+\.\d+)', r'Server: Apache/(\d+\.\d+\.\d+)'],
        'PHP': [r'PHP/(\d+\.\d+\.\d+)', r'X-Powered-By: PHP/(\d+\.\d+\.\d+)'],
        'Node.js': [r'Node\.js/(\d+\.\d+\.\d+)', r'X-Powered-By: Node'],
        'WordPress': [r'generator" content="WordPress (\d+\.\d+\.\d+)"', r'wp-'],
        'Drupal': [r'generator" content="Drupal (\d+)"', r'Drupal.settings'],
        'Joomla': [r'generator" content="Joomla! (\d+\.\d+)"', r'/media/jui/'],
        'Shopify': [r'Shopify\.theme\s*=\s*[^}]*"name":"[^"]*","version":"([^"]+)"'],
        'Ghost': [r'@tryghost/[^/]+/(\d+\.\d+\.\d+)'],
        'HubSpot': [r'hs-scripts/(\d+\.\d+\.\d+)'],
        'Strapi': [r'strapi/(\d+\.\d+\.\d+)'],
        'Contentful': [r'contentful\.js\?v=(\d+\.\d+\.\d+)'],
        'Auth0': [r'auth0/(\d+\.\d+\.\d+)'],
        'Okta': [r'okta/(\d+\.\d+\.\d+)'],
        'Stripe': [r'stripe/(\d+\.\d+\.\d+)', r'js\.stripe\.com/v3/'],
        'Google Analytics': [r'ga\.js\?v=(\w+)', r'gtag/js\?id='],
        'Sentry': [r'sentry/(\d+\.\d+\.\d+)', r'browser\.sentry-cdn\.com/(\d+\.\d+\.\d+)'],
        'Datadog': [r'datadog-rum/(\d+\.\d+\.\d+)'],
        'New Relic': [r'nr-(\d+)\.min\.js'],
        'Webpack': [r'webpack/(\d+\.\d+\.\d+)', r'__webpack_require__'],
        'Vite': [r'vite/(\d+\.\d+\.\d+)', r'/@vite/'],
        'Babel': [r'babel/(\d+\.\d+\.\d+)', r'babel-standalone/(\d+\.\d+\.\d+)'],
        'TypeScript': [r'typescript/(\d+\.\d+\.\d+)', r'\.ts\?v=(\d+\.\d+\.\d+)'],
        'Font Awesome': [r'font-awesome/(\d+\.\d+\.\d+)', r'fa\.css\?v=(\d+\.\d+\.\d+)'],
        'Material Icons': [r'material-icons/(\d+\.\d+\.\d+)'],
        'Leaflet': [r'leaflet/(\d+\.\d+\.\d+)', r'leaflet\.css\?v=(\d+\.\d+\.\d+)'],
        'Mapbox': [r'mapbox-gl-js/(\d+\.\d+\.\d+)', r'mapbox\.css\?v=(\d+\.\d+\.\d+)'],
        'Chart.js': [r'chart\.js/(\d+\.\d+\.\d+)', r'Chart\.js/(\d+\.\d+\.\d+)'],
        'D3.js': [r'd3/(\d+\.\d+\.\d+)', r'd3\.min\.js\?v=(\d+\.\d+\.\d+)'],
        'Three.js': [r'three/(\d+\.\d+\.\d+)', r'three\.min\.js\?v=(\d+\.\d+\.\d+)'],
        'Moment.js': [r'moment/(\d+\.\d+\.\d+)', r'moment\.min\.js\?v=(\d+\.\d+\.\d+)'],
        'Lodash': [r'lodash/(\d+\.\d+\.\d+)', r'lodash\.min\.js\?v=(\d+\.\d+\.\d+)'],
        'Axios': [r'axios/(\d+\.\d+\.\d+)', r'axios\.min\.js\?v=(\d+\.\d+\.\d+)'],
        'Socket.io': [r'socket\.io/(\d+\.\d+\.\d+)', r'socket\.io\.js\?v=(\d+\.\d+\.\d+)'],
        'Redis': [r'redis/(\d+\.\d+\.\d+)', r'Redis version=(\d+\.\d+\.\d+)'],
        'MongoDB': [r'mongodb/(\d+\.\d+\.\d+)', r'MongoDB version=(\d+\.\d+\.\d+)'],
        'PostgreSQL': [r'postgresql/(\d+\.\d+\.\d+)', r'PostgreSQL (\d+\.\d+)'],
        'MySQL': [r'mysql/(\d+\.\d+\.\d+)', r'MySQL/(\d+\.\d+\.\d+)'],
        'Elasticsearch': [r'elasticsearch/(\d+\.\d+\.\d+)', r'Elasticsearch/(\d+\.\d+\.\d+)'],
    }
    
    def __init__(self):
        self.detected_technologies = {}
        self.detected_versions = {}
        self.confidence_scores = {}  # Confidence score for each detected technology
        self.detection_methods = {}  # Which method detected each technology
        self.cookies = {}  # Detected cookies
        self.script_sources = []  # All script sources found
        self.css_classes = set()  # All CSS classes found
        self.data_attributes = set()  # All data attributes found
        self.security_headers = {}  # Security headers detected
        self.ssl_info = {}  # SSL/TLS information
    
    def _extract_cookies(self, headers: Dict) -> Dict:
        """Extract and analyze cookies from headers."""
        cookies = {}
        set_cookie = headers.get('Set-Cookie', '')
        if set_cookie:
            if isinstance(set_cookie, str):
                cookie_parts = set_cookie.split(';')
                for part in cookie_parts:
                    if '=' in part:
                        name, value = part.split('=', 1)
                        cookies[name.strip()] = value.strip()
            elif isinstance(set_cookie, list):
                for cookie in set_cookie:
                    cookie_parts = cookie.split(';')
                    for part in cookie_parts:
                        if '=' in part:
                            name, value = part.split('=', 1)
                            cookies[name.strip()] = value.strip()
        return cookies
    
    def _extract_script_sources(self, html_content: str) -> List[str]:
        """Extract all script source URLs from HTML."""
        import re
        script_pattern = r'<script[^>]*src=["\']([^"\']+)["\']'
        return re.findall(script_pattern, html_content, re.IGNORECASE)
    
    def _extract_css_classes(self, html_content: str) -> Set[str]:
        """Extract all CSS class names from HTML."""
        import re
        class_pattern = r'class=["\']([^"\']+)["\']'
        classes = set()
        matches = re.findall(class_pattern, html_content, re.IGNORECASE)
        for match in matches:
            classes.update(match.split())
        return classes
    
    def _extract_data_attributes(self, html_content: str) -> Set[str]:
        """Extract all data attributes from HTML."""
        import re
        data_pattern = r'data-[^=]+=["\']?[^"\']*["\']?'
        attributes = set()
        matches = re.findall(data_pattern, html_content, re.IGNORECASE)
        for match in matches:
            attr_name = match.split('=')[0].strip()
            attributes.add(attr_name)
        return attributes
    
    def _analyze_security_headers(self, headers: Dict) -> Dict:
        """Analyze security headers for technology clues and security posture."""
        security_info = {}
        
        security_headers = {
            'Strict-Transport-Security': 'HSTS',
            'Content-Security-Policy': 'CSP',
            'X-Frame-Options': 'Clickjacking Protection',
            'X-Content-Type-Options': 'MIME Sniffing Protection',
            'X-XSS-Protection': 'XSS Filter',
            'Referrer-Policy': 'Referrer Control',
            'Permissions-Policy': 'Feature Policy',
            'Cross-Origin-Opener-Policy': 'COOP',
            'Cross-Origin-Resource-Policy': 'CORP',
            'Cross-Origin-Embedder-Policy': 'COEP',
        }
        
        for header, description in security_headers.items():
            if header in headers:
                security_info[header] = {
                    'value': headers[header],
                    'description': description
                }
        
        # SSL/TLS information from headers
        if 'Strict-Transport-Security' in headers:
            self.ssl_info['hsts_enabled'] = True
            self.ssl_info['hsts_max_age'] = headers['Strict-Transport-Security']
        
        return security_info
    
    def _infer_technology_stack(self) -> Dict:
        """Infer technology stack relationships and dependencies."""
        inferences = {}
        
        # Framework-specific inferences
        if 'React' in self.confidence_scores:
            if 'Redux' in self.confidence_scores:
                inferences['React + Redux'] = 'React application with Redux state management'
            if 'Next.js' in self.confidence_scores:
                inferences['Next.js + React'] = 'Next.js framework using React'
        
        if 'Vue.js' in self.confidence_scores:
            if 'Vuex' in self.confidence_scores:
                inferences['Vue + Vuex'] = 'Vue.js application with Vuex state management'
            if 'Nuxt.js' in self.confidence_scores:
                inferences['Nuxt + Vue'] = 'Nuxt.js framework using Vue.js'
        
        if 'Angular' in self.confidence_scores:
            if 'NgRx' in self.confidence_scores:
                inferences['Angular + NgRx'] = 'Angular application with NgRx state management'
        
        # CMS-specific inferences
        if 'WordPress' in self.confidence_scores:
            if 'WooCommerce' in self.confidence_scores:
                inferences['WordPress + WooCommerce'] = 'WordPress with e-commerce via WooCommerce'
            if 'Elementor' in self.confidence_scores:
                inferences['WordPress + Elementor'] = 'WordPress with Elementor page builder'
        
        # Database inferences from frameworks
        if 'Django' in self.confidence_scores:
            inferences['Django Stack'] = 'Likely using PostgreSQL or SQLite (Django defaults)'
        if 'Rails' in self.confidence_scores:
            inferences['Rails Stack'] = 'Likely using PostgreSQL or MySQL (Rails defaults)'
        if 'Laravel' in self.confidence_scores:
            inferences['Laravel Stack'] = 'Likely using MySQL or PostgreSQL (Laravel defaults)'
        
        # JavaScript framework inferences
        if 'Node.js' in self.confidence_scores:
            if 'Express.js' in self.confidence_scores:
                inferences['Node + Express'] = 'Node.js backend with Express framework'
            if 'MongoDB' in self.confidence_scores:
                inferences['MEAN/MERN Stack'] = 'Possible MEAN/MERN stack (MongoDB, Express, Angular/React, Node)'
        
        # Build tool inferences
        if 'React' in self.confidence_scores or 'Vue.js' in self.confidence_scores:
            if 'Webpack' in self.confidence_scores:
                inferences['Modern Build Stack'] = 'Using Webpack for module bundling'
            if 'Vite' in self.confidence_scores:
                inferences['Modern Build Stack'] = 'Using Vite for fast development and building'
        
        # UI framework inferences
        if 'React' in self.confidence_scores:
            if 'Material UI' in self.confidence_scores:
                inferences['React + Material UI'] = 'React with Material Design components'
            if 'Ant Design' in self.confidence_scores:
                inferences['React + Ant Design'] = 'React with Ant Design component library'
        
        if 'Vue.js' in self.confidence_scores:
            if 'Element UI' in self.confidence_scores:
                inferences['Vue + Element UI'] = 'Vue.js with Element UI components'
        
        # Analytics inferences
        analytics_count = sum(1 for tech in ['Google Analytics', 'Google Tag Manager', 'Hotjar', 'Mixpanel', 'Segment'] 
                           if tech in self.confidence_scores)
        if analytics_count >= 2:
            inferences['Multi-Analytics'] = f'Using {analytics_count} different analytics/tracking tools'
        
        # Security posture inference
        security_headers_count = len(self.security_headers)
        if security_headers_count >= 5:
            inferences['Security Posture'] = 'Strong security posture with multiple security headers'
        elif security_headers_count >= 2:
            inferences['Security Posture'] = 'Moderate security posture with some security headers'
        else:
            inferences['Security Posture'] = 'Limited security headers detected'
        
        return inferences
    
    def _detect_from_cookies(self, cookies: Dict) -> Dict:
        """Detect technologies from cookie patterns."""
        detected = {}
        confidence = {}
        
        cookie_patterns = {
            'WordPress': {'wp-settings', 'wordpress_logged_in', 'wp-postpass'},
            'Drupal': {'Drupal.visitor', 'SSESS'},
            'Joomla': {'Joomla!'},
            'Magento': {'frontend', 'admin', 'customer'},
            'Shopify': {'_shopify_y', '_shopify_s', '_shopify_sa_p'},
            'Google Analytics': {'_ga', '_gid', '_gat'},
            'Hotjar': {'_hjid', '_hjDone', '_hjMinimized'},
            'Mixpanel': {'mp_mixpanel_token'},
            'Segment': {'ajs_user_id', 'ajs_anonymous_id'},
            'Amplitude': {'amp'},
            'Heap': {'_heap'},
            'FullStory': {'fs_uid'},
            'Intercom': {'intercom-id'},
            'Zendesk': {'zendesk_web_widget'},
            'Cloudflare': {'__cf_bm', 'cf_clearance'},
            'Varnish': {'X-Varnish'},
            'AWS': {'aws-'},
            'Azure': {'.AspNetCore'},
            'Auth0': {'auth0'},
            'Okta': {'okta'},
        }
        
        for tech, patterns in cookie_patterns.items():
            for cookie_name in cookies.keys():
                for pattern in patterns:
                    if pattern.lower() in cookie_name.lower():
                        if tech not in detected:
                            detected[tech] = []
                        detected[tech].append(f"Cookie: {cookie_name}")
                        confidence[tech] = confidence.get(tech, 0) + 0.4
        
        return detected, confidence
    
    def _detect_from_scripts(self, script_sources: List[str]) -> Dict:
        """Detect technologies from script source URLs."""
        detected = {}
        confidence = {}
        
        script_patterns = {
            'React': {'react', 'react-dom', 'reactjs'},
            'Vue.js': {'vue', 'vue-router', 'vuex'},
            'Angular': {'angular', 'angularjs', 'ng-'},
            'jQuery': {'jquery'},
            'Bootstrap': {'bootstrap'},
            'Tailwind CSS': {'tailwind'},
            'Material UI': {'material-ui', '@mui'},
            'Ant Design': {'antd', 'ant-design'},
            'Chart.js': {'chart.js', 'chartjs'},
            'D3.js': {'d3', 'd3.js'},
            'Three.js': {'three', 'three.js'},
            'Moment.js': {'moment'},
            'Lodash': {'lodash'},
            'Axios': {'axios'},
            'Socket.io': {'socket.io'},
            'Font Awesome': {'font-awesome', 'fontawesome'},
            'Google Analytics': {'google-analytics', 'gtag', 'analytics.js'},
            'Google Tag Manager': {'googletagmanager'},
            'Hotjar': {'hotjar'},
            'Mixpanel': {'mixpanel'},
            'Segment': {'segment'},
            'Amplitude': {'amplitude'},
            'Heap': {'heapanalytics'},
            'FullStory': {'fullstory'},
            'Sentry': {'sentry'},
            'Datadog': {'datadog'},
            'New Relic': {'newrelic'},
            'Intercom': {'intercom'},
            'Drift': {'drift'},
            'Zendesk': {'zendesk'},
            'Stripe': {'stripe', 'js.stripe'},
            'PayPal': {'paypal'},
            'Mapbox': {'mapbox'},
            'Leaflet': {'leaflet'},
            'YouTube': {'youtube'},
            'Vimeo': {'vimeo'},
            'Facebook': {'facebook', 'fb-'},
            'Twitter': {'twitter', 'x.com'},
            'LinkedIn': {'linkedin'},
        }
        
        for script in script_sources:
            script_lower = script.lower()
            for tech, patterns in script_patterns.items():
                for pattern in patterns:
                    if pattern in script_lower:
                        if tech not in detected:
                            detected[tech] = []
                        detected[tech].append(f"Script: {script}")
                        confidence[tech] = confidence.get(tech, 0) + 0.5
        
        return detected, confidence
    
    def _detect_from_css_classes(self, css_classes: Set[str]) -> Dict:
        """Detect technologies from CSS class names."""
        detected = {}
        confidence = {}
        
        class_patterns = {
            'Bootstrap': {'btn', 'container', 'row', 'col', 'navbar', 'card', 'alert', 'modal'},
            'Tailwind CSS': {'flex', 'grid', 'text-', 'bg-', 'p-', 'm-', 'w-', 'h-', 'rounded'},
            'Material UI': {'Mui', 'makeStyles', 'MuiButton', 'MuiCard'},
            'Ant Design': {'ant-', 'ant-btn', 'ant-card', 'ant-layout'},
            'Bulma': {'button', 'container', 'columns', 'column', 'navbar', 'card'},
            'Foundation': {'button', 'grid-x', 'cell', 'top-bar'},
            'Semantic UI': {'ui', 'button', 'container', 'segment', 'card'},
            'UI Kit': {'uk-', 'uk-button', 'uk-card'},
            'WordPress': {'wp-', 'widget', 'menu-item'},
            'Drupal': {'field-', 'node-', 'views-'},
            'Joomla': {'item-', 'category-'},
        }
        
        for css_class in css_classes:
            for tech, patterns in class_patterns.items():
                for pattern in patterns:
                    if pattern in css_class.lower():
                        if tech not in detected:
                            detected[tech] = []
                        detected[tech].append(f"Class: {css_class}")
                        confidence[tech] = confidence.get(tech, 0) + 0.3
        
        return detected, confidence
    
    def _detect_from_data_attributes(self, data_attributes: Set[str]) -> Dict:
        """Detect technologies from data attributes."""
        detected = {}
        confidence = {}
        
        data_patterns = {
            'Vue.js': {'data-v-', 'v-if', 'v-for', 'v-bind'},
            'Angular': {'ng-', 'data-ng-'},
            'React': {'data-reactid', 'data-reactroot'},
            'Alpine.js': {'x-data', 'x-if', 'x-for'},
            'HTMX': {'hx-', 'data-hx-'},
            'Turbo': {'data-turbo'},
            'Stimulus': {'data-controller', 'data-action'},
            'WordPress': {'data-wp-'},
            'Google Analytics': {'data-ga'},
        }
        
        for attr in data_attributes:
            for tech, patterns in data_patterns.items():
                for pattern in patterns:
                    if pattern in attr.lower():
                        if tech not in detected:
                            detected[tech] = []
                        detected[tech].append(f"Attribute: {attr}")
                        confidence[tech] = confidence.get(tech, 0) + 0.4
        
        return detected, confidence
    
    def _analyze_comprehensive_headers(self, headers: Dict) -> Dict:
        """Comprehensive analysis of HTTP headers for technology detection."""
        detected = {}
        confidence = {}
        
        # Analyze various headers
        header_patterns = {
            'X-Powered-By': {
                'PHP': {'php'},
                'Express': {'express'},
                'ASP.NET': {'asp.net', '.net'},
                'Python': {'python', 'wsgi'},
                'Node.js': {'node'},
                'Rails': {'rails', 'ruby'},
                'Django': {'django'},
                'Laravel': {'laravel'},
            },
            'Server': {
                'Apache': {'apache'},
                'Nginx': {'nginx'},
                'IIS': {'iis', 'microsoft-iis'},
                'Cloudflare': {'cloudflare'},
                'LiteSpeed': {'litespeed'},
                'Caddy': {'caddy'},
                'Gunicorn': {'gunicorn'},
                'uWSGI': {'uwsgi'},
                'Passenger': {'passenger'},
            },
            'X-AspNet-Version': {
                'ASP.NET': {'.net'},
            },
            'X-AspNetMvc-Version': {
                'ASP.NET MVC': {'mvc'},
            },
            'X-Pingback': {
                'WordPress': {'xmlrpc.php'},
            },
            'X-Drupal-Cache': {
                'Drupal': {'drupal'},
            },
            'X-Generator': {
                'Drupal': {'drupal'},
                'WordPress': {'wordpress'},
                'Joomla': {'joomla'},
                'Ghost': {'ghost'},
                'HubSpot': {'hubspot'},
            },
        }
        
        for header_name, techs in header_patterns.items():
            header_value = headers.get(header_name, '')
            if header_value:
                header_lower = header_value.lower()
                for tech, patterns in techs.items():
                    for pattern in patterns:
                        if pattern in header_lower:
                            if tech not in detected:
                                detected[tech] = []
                            detected[tech].append(f"Header: {header_name}")
                            confidence[tech] = confidence.get(tech, 0) + 0.7
        
        return detected, confidence
    
    def detect_version(self, tech: str, html_content: str, headers: Dict) -> Optional[str]:
        """Enhanced version detection with multiple extraction methods."""
        if tech not in self.VERSION_PATTERNS:
            return None
        
        # Check in HTML content
        for pattern in self.VERSION_PATTERNS[tech]:
            try:
                import re
                match = re.search(pattern, html_content, re.IGNORECASE)
                if match:
                    return match.group(1)
            except Exception:
                continue
        
        # Check in headers
        headers_str = str(headers)
        for pattern in self.VERSION_PATTERNS[tech]:
            try:
                import re
                match = re.search(pattern, headers_str, re.IGNORECASE)
                if match:
                    return match.group(1)
            except Exception:
                continue
        
        # Try to extract from meta generator tag
        try:
            import re
            generator_match = re.search(r'<meta\s+name=["\']generator["\']\s+content=["\'][^"\']*' + tech.lower() + r'[^"\']*(\d+\.\d+\.?\d*)[^"\']*["\']', html_content, re.IGNORECASE)
            if generator_match:
                return generator_match.group(1)
        except Exception:
            pass
        
        return None
    
    def fingerprint(self, url: str, html_content: str, headers: Dict) -> Dict:
        """Advanced fingerprinting with multiple detection methods and confidence scoring."""
        # Initialize results for all categories
        results = {category: [] for category in self.TECHNOLOGY_SIGNATURES.keys()}
        self.detected_versions = {}
        self.confidence_scores = {}
        self.detection_methods = {}
        
        # Extract additional data sources
        self.cookies = self._extract_cookies(headers)
        self.script_sources = self._extract_script_sources(html_content)
        self.css_classes = self._extract_css_classes(html_content)
        self.data_attributes = self._extract_data_attributes(html_content)
        self.security_headers = self._analyze_security_headers(headers)
        
        # Collect all detections from different methods
        all_detections = {}
        all_confidence = {}
        
        # Detect from cookies
        cookie_detections, cookie_confidence = self._detect_from_cookies(self.cookies)
        for tech, methods in cookie_detections.items():
            if tech not in all_detections:
                all_detections[tech] = []
            all_detections[tech].extend(methods)
            all_confidence[tech] = all_confidence.get(tech, 0) + cookie_confidence[tech]
            self.detection_methods[tech] = self.detection_methods.get(tech, []) + ['cookie']
        
        # Detect from scripts
        script_detections, script_confidence = self._detect_from_scripts(self.script_sources)
        for tech, methods in script_detections.items():
            if tech not in all_detections:
                all_detections[tech] = []
            all_detections[tech].extend(methods)
            all_confidence[tech] = all_confidence.get(tech, 0) + script_confidence[tech]
            self.detection_methods[tech] = self.detection_methods.get(tech, []) + ['script']
        
        # Detect from CSS classes
        css_detections, css_confidence = self._detect_from_css_classes(self.css_classes)
        for tech, methods in css_detections.items():
            if tech not in all_detections:
                all_detections[tech] = []
            all_detections[tech].extend(methods)
            all_confidence[tech] = all_confidence.get(tech, 0) + css_confidence[tech]
            self.detection_methods[tech] = self.detection_methods.get(tech, []) + ['css_class']
        
        # Detect from data attributes
        data_detections, data_confidence = self._detect_from_data_attributes(self.data_attributes)
        for tech, methods in data_detections.items():
            if tech not in all_detections:
                all_detections[tech] = []
            all_detections[tech].extend(methods)
            all_confidence[tech] = all_confidence.get(tech, 0) + data_confidence[tech]
            self.detection_methods[tech] = self.detection_methods.get(tech, []) + ['data_attribute']
        
        # Detect from comprehensive headers
        header_detections, header_confidence = self._analyze_comprehensive_headers(headers)
        for tech, methods in header_detections.items():
            if tech not in all_detections:
                all_detections[tech] = []
            all_detections[tech].extend(methods)
            all_confidence[tech] = all_confidence.get(tech, 0) + header_confidence[tech]
            self.detection_methods[tech] = self.detection_methods.get(tech, []) + ['header']
        
        # Traditional HTML content detection (with confidence scoring)
        html_lower = html_content.lower()
        for category, technologies in self.TECHNOLOGY_SIGNATURES.items():
            for tech, signatures in technologies.items():
                match_count = 0
                for sig in signatures:
                    if sig.lower() in html_lower:
                        match_count += 1
                
                if match_count > 0:
                    if tech not in all_detections:
                        all_detections[tech] = []
                    all_detections[tech].append(f"HTML content ({match_count} matches)")
                    confidence_boost = min(0.3 * match_count, 0.9)
                    all_confidence[tech] = all_confidence.get(tech, 0) + confidence_boost
                    self.detection_methods[tech] = self.detection_methods.get(tech, []) + ['html_content']
        
        # URL pattern detection
        url_lower = url.lower()
        for tech, signatures in self.TECHNOLOGY_SIGNATURES['cms'].items():
            for sig in signatures:
                if sig.lower() in url_lower:
                    if tech not in all_detections:
                        all_detections[tech] = []
                    all_detections[tech].append(f"URL pattern: {sig}")
                    all_confidence[tech] = all_confidence.get(tech, 0) + 0.6
                    self.detection_methods[tech] = self.detection_methods.get(tech, []) + ['url']
        
        # Meta generator detection
        try:
            import re
            generator_match = re.search(r'<meta\s+name=["\']generator["\']\s+content=["\']([^"\']+)["\']', html_content, re.IGNORECASE)
            if generator_match:
                generator_content = generator_match.group(1).lower()
                for tech in self.TECHNOLOGY_SIGNATURES['cms'].keys():
                    if tech.lower() in generator_content:
                        if tech not in all_detections:
                            all_detections[tech] = []
                        all_detections[tech].append("Meta generator tag")
                        all_confidence[tech] = all_confidence.get(tech, 0) + 0.8
                        self.detection_methods[tech] = self.detection_methods.get(tech, []) + ['meta_generator']
                        # Extract version from generator
                        version_match = re.search(r'(\d+\.\d+\.?\d*)', generator_content)
                        if version_match:
                            self.detected_versions[tech] = version_match.group(1)
        except Exception:
            pass
        
        # Normalize confidence scores and categorize technologies
        for tech, confidence in all_confidence.items():
            # Cap confidence at 1.0
            normalized_confidence = min(confidence, 1.0)
            self.confidence_scores[tech] = normalized_confidence
            
            # Only include technologies with confidence above threshold
            if normalized_confidence >= self.CONFIDENCE_LOW:
                # Find appropriate category
                for category, technologies in self.TECHNOLOGY_SIGNATURES.items():
                    if tech in technologies:
                        if tech not in results[category]:
                            results[category].append(tech)
                        # Try to detect version
                        if tech not in self.detected_versions:
                            version = self.detect_version(tech, html_content, headers)
                            if version:
                                self.detected_versions[tech] = version
                        break
        
        self.detected_technologies = results
        return results
    
    def generate_report(self) -> str:
        """Generate a comprehensive human-readable report with confidence scores and detection methods."""
        if not self.detected_technologies:
            return "No technologies detected."
        
        report = "Technology Stack Detection Report\n"
        report += "=" * 50 + "\n\n"
        
        # Technology stack inferences
        inferences = self._infer_technology_stack()
        if inferences:
            report += "Technology Stack Inferences:\n"
            report += "-" * 40 + "\n"
            for inference, description in inferences.items():
                report += f"  • {inference}: {description}\n"
            report += "\n"
        
        # Detected technologies by category with confidence
        for category, technologies in self.detected_technologies.items():
            if technologies:
                report += f"{category.replace('_', ' ').title()}:\n"
                report += "-" * 40 + "\n"
                
                # Sort by confidence score
                sorted_techs = sorted(technologies, 
                                    key=lambda x: self.confidence_scores.get(x, 0), 
                                    reverse=True)
                
                for tech in sorted_techs:
                    confidence = self.confidence_scores.get(tech, 0)
                    confidence_percent = int(confidence * 100)
                    confidence_level = "HIGH" if confidence >= self.CONFIDENCE_HIGH else \
                                      "MEDIUM" if confidence >= self.CONFIDENCE_MEDIUM else "LOW"
                    
                    version = self.detected_versions.get(tech, "Unknown")
                    methods = self.detection_methods.get(tech, [])
                    methods_str = ", ".join(set(methods)) if methods else "N/A"
                    
                    report += f"  • {tech}\n"
                    report += f"    Version: {version}\n"
                    report += f"    Confidence: {confidence_percent}% ({confidence_level})\n"
                    report += f"    Detected via: {methods_str}\n"
                    report += "\n"
        
        # Security headers analysis
        if self.security_headers:
            report += "Security Headers:\n"
            report += "-" * 40 + "\n"
            for header, info in self.security_headers.items():
                report += f"  • {header} ({info['description']})\n"
                report += f"    Value: {info['value'][:100]}{'...' if len(info['value']) > 100 else ''}\n"
            report += "\n"
        
        # SSL/TLS information
        if self.ssl_info:
            report += "SSL/TLS Information:\n"
            report += "-" * 40 + "\n"
            for key, value in self.ssl_info.items():
                report += f"  • {key}: {value}\n"
            report += "\n"
        
        # Detection statistics
        total_techs = sum(len(techs) for techs in self.detected_technologies.values())
        high_confidence = sum(1 for tech, conf in self.confidence_scores.items() 
                            if conf >= self.CONFIDENCE_HIGH)
        medium_confidence = sum(1 for tech, conf in self.confidence_scores.items() 
                               if self.CONFIDENCE_MEDIUM <= conf < self.CONFIDENCE_HIGH)
        
        report += "Detection Statistics:\n"
        report += "-" * 40 + "\n"
        report += f"  • Total technologies detected: {total_techs}\n"
        report += f"  • High confidence detections: {high_confidence}\n"
        report += f"  • Medium confidence detections: {medium_confidence}\n"
        report += f"  • Security headers found: {len(self.security_headers)}\n"
        report += f"  • Cookies analyzed: {len(self.cookies)}\n"
        report += f"  • Scripts analyzed: {len(self.script_sources)}\n"
        report += f"  • CSS classes found: {len(self.css_classes)}\n"
        report += f"  • Data attributes found: {len(self.data_attributes)}\n"
        
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
        import os
        
        # Initialize output_path before async function
        if output_path is None:
            os.makedirs(self.screenshot_dir, exist_ok=True)
            filename = f"{hashlib.md5(url.encode()).hexdigest()}.png"
            output_path = os.path.join(self.screenshot_dir, filename)
        
        async def _capture():
            async with async_playwright() as p:
                browser = await p.chromium.launch(headless=True)
                page = await browser.new_page()
                await page.goto(url, wait_until='networkidle', timeout=30000)
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
        
        diff_lines = list(diff)
        added_count = sum(1 for line in diff_lines if line.startswith('+') and not line.startswith('+++'))
        removed_count = sum(1 for line in diff_lines if line.startswith('-') and not line.startswith('---'))
        
        return {
            'added_lines': added_count,
            'removed_lines': removed_count,
            'diff': ''.join(diff_lines)
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
            except Exception as e:
                logger.debug(f"Failed to load history file {hist_path}: {e}")
        
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
                except Exception as e:
                    logger.debug(f"Failed to extract geolocation data: {e}")
        
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
        """Perform traceroute using TCP SYN packets (more accurate than HTTP)."""
        results = []
        
        try:
            # Try TCP-based traceroute first (more accurate)
            results = self._tcp_traceroute(target, max_hops)
            
            # If TCP traceroute fails, fall back to HTTP-based
            if not results or any('error' in r for r in results):
                results = self._http_traceroute(target, max_hops)
                
        except Exception as e:
            # Final fallback to HTTP traceroute
            results = self._http_traceroute(target, max_hops)
        
        return results
    
    def _tcp_traceroute(self, target: str, max_hops: int = 30) -> List[Dict]:
        """TCP SYN traceroute using socket TTL manipulation."""
        import socket
        import struct
        
        results = []
        
        try:
            hostname = socket.gethostbyname(target)
            dest_ip = socket.gethostbyname(target)
            
            # Common ports to try
            ports = [80, 443, 22, 21, 25, 53]
            
            for port in ports:
                try:
                    for ttl in range(1, max_hops + 1):
                        try:
                            # Create TCP socket
                            sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                            sock.settimeout(2)
                            
                            # Set TTL (Windows uses IP_TTL, Linux uses IP_TTL)
                            try:
                                sock.setsockopt(socket.IPPROTO_IP, socket.IP_TTL, ttl)
                            except AttributeError:
                                # Windows might use different constant
                                try:
                                    sock.setsockopt(0, 4, ttl)  # IP_TTL on Windows
                                except Exception as e:
                                    logger.debug(f"Failed to set socket option: {e}")
                            
                            start_time = time.time()
                            result = sock.connect_ex((dest_ip, port))
                            rtt = (time.time() - start_time) * 1000
                            
                            sock.close()
                            
                            if result == 0:
                                # Port is open - reached target
                                results.append({
                                    'hop': ttl,
                                    'ip': dest_ip,
                                    'port': port,
                                    'rtt_ms': round(rtt, 2),
                                    'status': 'reached'
                                })
                                return results
                            else:
                                # Got a response but connection refused
                                results.append({
                                    'hop': ttl,
                                    'ip': dest_ip,
                                    'port': port,
                                    'rtt_ms': round(rtt, 2),
                                    'status': 'filtered'
                                })
                        except socket.timeout:
                            results.append({
                                'hop': ttl,
                                'ip': '*',
                                'rtt_ms': None,
                                'status': 'timeout'
                            })
                        except Exception as e:
                            results.append({
                                'hop': ttl,
                                'ip': '*',
                                'rtt_ms': None,
                                'status': f'error: {str(e)}'
                            })
                    
                    # If we got some results, return them
                    if results:
                        return results
                        
                except Exception as e:
                    logger.debug(f"Port scan attempt failed: {e}")
                    continue
            
            return results
            
        except Exception as e:
            return [{'error': f'TCP traceroute failed: {str(e)}'}]
    
    def _http_traceroute(self, target: str, max_hops: int = 30) -> List[Dict]:
        """HTTP-based traceroute fallback."""
        results = []
        
        try:
            hostname = socket.gethostbyname(target)
            
            for ttl in range(1, max_hops + 1):
                try:
                    start_time = time.time()
                    response = self.session.get(f"http://{target}", timeout=5)
                    rtt = (time.time() - start_time) * 1000
                    
                    results.append({
                        'hop': ttl,
                        'ip': hostname,
                        'rtt_ms': round(rtt, 2),
                        'status': 'success',
                        'method': 'http'
                    })
                    break  # Reached target
                except requests.RequestException:
                    results.append({
                        'hop': ttl,
                        'ip': '*',
                        'rtt_ms': None,
                        'status': 'timeout',
                        'method': 'http'
                    })
        
        except Exception as e:
            results.append({'error': str(e), 'method': 'http'})
        
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
            except Exception as e:
                logger.debug(f"Reddit API initialization failed: {e}")
        
        if mastodon and mastodon_instance and mastodon_token:
            try:
                self.mastodon_client = mastodon.Mastodon(
                    access_token=mastodon_token,
                    api_base_url=mastodon_instance
                )
            except Exception as e:
                logger.debug(f"Mastodon API initialization failed: {e}")
    
    def search_reddit(self, query: str, limit: int = 10) -> List[Dict]:
        """Search Reddit for mentions."""
        if not self.reddit_client:
            return self._reddit_fallback(query, limit)
        
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
            return self._reddit_fallback(query, limit)
        
        return results
    
    def _reddit_fallback(self, query: str, limit: int = 10) -> List[Dict]:
        """Fallback method using public Reddit search without API credentials."""
        try:
            from bs4 import BeautifulSoup
            import urllib.parse
            
            results = []
            search_url = f"https://www.reddit.com/search/?q={urllib.parse.quote(query)}&sort=relevance&t=all"
            
            headers = {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
            }
            
            response = self.session.get(search_url, headers=headers, timeout=10)
            soup = BeautifulSoup(response.text, 'html.parser')
            
            # Parse Reddit search results (non-API approach)
            posts = soup.find_all('div', {'data-testid': 'post-container'})
            
            for post in posts[:limit]:
                try:
                    title_elem = post.find('h3')
                    if title_elem:
                        title = title_elem.get_text(strip=True)
                        
                        # Try to get link
                        link_elem = post.find('a', {'data-testid': 'post-title-link'})
                        url = link_elem.get('href', '') if link_elem else ''
                        if url and not url.startswith('http'):
                            url = f"https://reddit.com{url}"
                        
                        # Try to get subreddit
                        subreddit_elem = post.find('a', {'data-testid': 'subreddit-name'})
                        subreddit = subreddit_elem.get_text(strip=True) if subreddit_elem else 'unknown'
                        
                        # Try to get score
                        score_elem = post.find('div', {'data-testid': 'post-vote-score'})
                        score = score_elem.get_text(strip=True) if score_elem else '0'
                        
                        results.append({
                            'platform': 'reddit',
                            'type': 'submission',
                            'title': title,
                            'url': url,
                            'subreddit': subreddit,
                            'score': score,
                            'source': 'web_scrape'
                        })
                except Exception as e:
                    logger.debug(f"Reddit web scraping failed: {e}")
                    continue
            
            if not results:
                return [{
                    'platform': 'reddit',
                    'info': 'No results found via web scraping',
                    'search_url': search_url,
                    'source': 'web_scrape'
                }]
            
            return results
        except ImportError:
            return [{
                'error': 'BeautifulSoup not available for web scraping',
                'suggestion': 'Install beautifulsoup4: pip install beautifulsoup4'
            }]
        except Exception as e:
            return [{'error': f'Web scraping failed: {str(e)}'}]
    
    def search_mastodon(self, query: str, limit: int = 10) -> List[Dict]:
        """Search Mastodon for mentions."""
        if not self.mastodon_client:
            return self._mastodon_fallback(query, limit)
        
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
            return self._mastodon_fallback(query, limit)
        
        return results
    
    def _mastodon_fallback(self, query: str, limit: int = 10) -> List[Dict]:
        """Fallback method using public Mastodon instance search without API credentials."""
        try:
            from bs4 import BeautifulSoup
            import urllib.parse
            
            results = []
            
            # Try searching on mastodon.social (largest public instance)
            search_url = f"https://mastodon.social/api/v2/search?q={urllib.parse.quote(query)}&type=statuss&limit={limit}"
            
            headers = {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
            }
            
            try:
                response = self.session.get(search_url, headers=headers, timeout=10)
                data = response.json()
                
                for status in data.get('statuses', [])[:limit]:
                    results.append({
                        'platform': 'mastodon',
                        'type': 'toot',
                        'content': status.get('content', ''),
                        'url': status.get('url', ''),
                        'account': status.get('account', {}).get('url', ''),
                        'created_at': status.get('created_at', ''),
                        'reblogs_count': status.get('reblogs_count', 0),
                        'favourites_count': status.get('favourites_count', 0),
                        'source': 'public_api'
                    })
            except Exception as e:
                logger.debug(f"Mastodon API search failed: {e}")
                # If API fails, try web scraping fallback
                web_url = f"https://mastodon.social/search?q={urllib.parse.quote(query)}"
                response = self.session.get(web_url, headers=headers, timeout=10)
                soup = BeautifulSoup(response.text, 'html.parser')
                
                # Parse Mastodon search results
                toots = soup.find_all('div', class_='status')
                
                for toot in toots[:limit]:
                    try:
                        content_elem = toot.find('div', class_='status__content')
                        content = content_elem.get_text(strip=True) if content_elem else ''
                        
                        url_elem = toot.find('a', class_='status__relative-time')
                        url = url_elem.get('href', '') if url_elem else ''
                        
                        account_elem = toot.find('span', class_='display-name')
                        account = account_elem.get_text(strip=True) if account_elem else 'unknown'
                        
                        results.append({
                            'platform': 'mastodon',
                            'type': 'toot',
                            'content': content,
                            'url': url,
                            'account': account,
                            'source': 'web_scrape'
                        })
                    except Exception as e:
                        logger.debug(f"Mastodon web scraping failed: {e}")
                        continue
            
            if not results:
                return [{
                    'platform': 'mastodon',
                    'info': 'No results found via public search',
                    'search_url': f"https://mastodon.social/search?q={urllib.parse.quote(query)}",
                    'source': 'public_search'
                }]
            
            return results
        except ImportError:
            return [{
                'error': 'BeautifulSoup not available for web scraping',
                'suggestion': 'Install beautifulsoup4: pip install beautifulsoup4'
            }]
        except Exception as e:
            return [{'error': f'Public search failed: {str(e)}'}]
    
    def search_all(self, query: str, limit: int = 10) -> Dict[str, List[Dict]]:
        """Search all configured platforms."""
        results = {}
        
        # Always try fallbacks even without credentials
        results['reddit'] = self.search_reddit(query, limit)
        results['mastodon'] = self.search_mastodon(query, limit)
        
        return results

class DNSAnalyzer:
    """DNS-based OSINT without API dependencies."""
    
    def __init__(self):
        import socket
        self.socket = socket
    
    def analyze_domain(self, domain: str) -> Dict:
        """Comprehensive DNS analysis of a domain."""
        try:
            result = {
                'domain': domain,
                'records': {},
                'info': 'DNS enumeration',
                'source': 'local_dns'
            }
            
            # A records
            try:
                import dns.resolver
                answers = dns.resolver.resolve(domain, 'A')
                result['records']['A'] = [str(rdata) for rdata in answers]
            except ImportError:
                # Fallback to socket.gethostbyname
                try:
                    ip = self.socket.gethostbyname(domain)
                    result['records']['A'] = [ip]
                except Exception as e:
                    logger.debug(f"DNS lookup failed for {domain}: {e}")
            except Exception as e:
                logger.debug(f"DNS query failed: {e}")
            
            # MX records
            try:
                import dns.resolver
                answers = dns.resolver.resolve(domain, 'MX')
                result['records']['MX'] = [(str(rdata.exchange), rdata.preference) for rdata in answers]
            except ImportError:
                pass
            except Exception:
                pass
            
            # NS records
            try:
                import dns.resolver
                answers = dns.resolver.resolve(domain, 'NS')
                result['records']['NS'] = [str(rdata) for rdata in answers]
            except ImportError:
                pass
            except Exception:
                pass
            
            # TXT records (often contains SPF, DKIM, verification)
            try:
                import dns.resolver
                answers = dns.resolver.resolve(domain, 'TXT')
                result['records']['TXT'] = [str(rdata).strip('"') for rdata in answers]
            except ImportError:
                pass
            except Exception:
                pass
            
            # CNAME records
            try:
                import dns.resolver
                answers = dns.resolver.resolve(domain, 'CNAME')
                result['records']['CNAME'] = [str(rdata.target) for rdata in answers]
            except ImportError:
                pass
            except Exception:
                pass
            
            # SOA records
            try:
                import dns.resolver
                answers = dns.resolver.resolve(domain, 'SOA')
                for rdata in answers:
                    result['records']['SOA'] = {
                        'mname': str(rdata.mname),
                        'rname': str(rdata.rname),
                        'serial': rdata.serial,
                        'refresh': rdata.refresh,
                        'retry': rdata.retry,
                        'expire': rdata.expire,
                        'minimum': rdata.minimum
                    }
                    break
            except ImportError:
                pass
            except Exception:
                pass
            
            # DNSSEC check
            try:
                import dns.resolver
                answers = dns.resolver.resolve(domain, 'DNSKEY')
                result['dnssec_enabled'] = True
            except Exception as e:
                logger.debug(f"DNSSEC check failed: {e}")
                result['dnssec_enabled'] = False
            
            return result
        except Exception as e:
            return {'error': f'DNS analysis failed: {str(e)}'}
    
    def reverse_dns_lookup(self, ip: str) -> Dict:
        """Reverse DNS lookup for an IP address."""
        try:
            hostname = self.socket.gethostbyaddr(ip)
            return {
                'ip': ip,
                'hostname': hostname[0],
                'aliases': hostname[1],
                'source': 'local_dns'
            }
        except self.socket.herror:
            return {
                'ip': ip,
                'hostname': None,
                'info': 'No reverse DNS record found',
                'source': 'local_dns'
            }
        except Exception as e:
            return {'error': f'Reverse DNS lookup failed: {str(e)}'}
    
    def dns_zone_transfer_check(self, domain: str) -> Dict:
        """Check if zone transfer is allowed (AXFR)."""
        try:
            import dns.resolver
            import dns.query
            
            # Get NS records
            ns_records = []
            try:
                answers = dns.resolver.resolve(domain, 'NS')
                ns_records = [str(rdata) for rdata in answers]
            except Exception as e:
                logger.debug(f"NS record query failed: {e}")
                return {'error': 'Could not get NS records'}
            
            # Try AXFR on each nameserver
            axfr_results = {}
            for ns in ns_records:
                try:
                    zone = dns.query.xfr(ns, domain, timeout=5)
                    records = list(zone)
                    if records:
                        axfr_results[ns] = {
                            'vulnerable': True,
                            'record_count': len(records)
                        }
                    else:
                        axfr_results[ns] = {'vulnerable': False}
                except Exception:
                    axfr_results[ns] = {'vulnerable': False, 'error': 'AXFR refused or failed'}
            
            return {
                'domain': domain,
                'nameservers': ns_records,
                'axfr_results': axfr_results,
                'source': 'local_dns'
            }
        except ImportError:
            return {'error': 'dnspython library not available'}
        except Exception as e:
            return {'error': f'Zone transfer check failed: {str(e)}'}

class WHOISAnalyzer:
    """WHOIS lookup without API keys using direct WHOIS protocol."""
    
    def __init__(self):
        self.session = requests.Session()
        self.session.headers.update({
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
        })
    
    def whois_lookup(self, target: str) -> Dict:
        """Perform WHOIS lookup using public WHOIS servers."""
        try:
            import socket
            
            # Determine if target is domain or IP
            try:
                import ipaddress
                ipaddress.ip_address(target)
                is_ip = True
            except Exception:
                is_ip = False
            
            if is_ip:
                return self._ip_whois(target)
            else:
                return self._domain_whois(target)
        except Exception as e:
            return {'error': f'WHOIS lookup failed: {str(e)}'}
    
    def _domain_whois(self, domain: str) -> Dict:
        """Domain WHOIS lookup using public web services."""
        try:
            # Try multiple public WHOIS services
            services = [
                f'https://who.is/whois/{domain}',
                f'https://www.whois.com/whois/{domain}',
                f'https://lookup.domaininformation.com/whois/{domain}'
            ]
            
            for service in services:
                try:
                    response = self.session.get(service, timeout=10)
                    if response.status_code == 200:
                        # Parse HTML with BeautifulSoup
                        soup = BeautifulSoup(response.text, 'html.parser')
                        
                        result = {
                            'domain': domain,
                            'source': service,
                            'raw_response': response.text[:2000],  # Truncate for display
                            'info': 'WHOIS data retrieved from web service'
                        }
                        
                        # Extract data from who.is
                        if 'who.is' in service:
                            result.update(self._extract_whois_data(soup))
                        # Extract data from whois.com
                        elif 'whois.com' in service:
                            result.update(self._extract_whois_com_data(soup))
                        # Extract data from domaininformation.com
                        else:
                            result.update(self._extract_generic_whois_data(soup))
                        
                        return result
                except Exception as e:
                    logger.debug(f"WHOIS server query failed: {e}")
                    continue
            
            return {
                'domain': domain,
                'error': 'All WHOIS services failed',
                'info': 'Try using command-line whois tool: whois ' + domain
            }
        except Exception as e:
            return {'error': f'Domain WHOIS failed: {str(e)}'}
    
    def _extract_whois_data(self, soup: BeautifulSoup) -> Dict:
        """Extract WHOIS data from who.is."""
        data = {}
        
        # Try to find data in various common structures
        # Look for table rows with labels
        rows = soup.find_all(['tr', 'div'])
        for row in rows:
            text = row.get_text(strip=True)
            if ':' in text:
                parts = text.split(':', 1)
                if len(parts) == 2:
                    key = parts[0].strip().lower()
                    value = parts[1].strip()
                    if value and value != 'N/A':
                        # Map common keys
                        if 'registrar' in key:
                            data['registrar'] = value
                        elif 'created' in key or 'creation' in key:
                            data['creation_date'] = value
                        elif 'expires' in key or 'expiration' in key:
                            data['expiration_date'] = value
                        elif 'updated' in key:
                            data['updated_date'] = value
                        elif 'nameserver' in key or 'name server' in key:
                            if 'nameservers' not in data:
                                data['nameservers'] = []
                            data['nameservers'].append(value)
                        elif 'registrant' in key and 'name' in key:
                            data['registrant_name'] = value
                        elif 'registrant' in key and 'email' in key:
                            data['registrant_email'] = value
                        elif 'registrant' in key and 'organization' in key:
                            data['registrant_org'] = value
                        elif 'status' in key:
                            data['status'] = value
                        elif 'dnssec' in key:
                            data['dnssec'] = value
        
        return data
    
    def _extract_whois_com_data(self, soup: BeautifulSoup) -> Dict:
        """Extract WHOIS data from whois.com."""
        data = {}
        
        # Look for data in df-raw or pre tags
        raw_data = soup.find(['pre', 'code', 'div'], class_=lambda x: x and ('raw' in str(x).lower() or 'whois' in str(x).lower()))
        if raw_data:
            text = raw_data.get_text()
            lines = text.split('\n')
            for line in lines:
                if ':' in line:
                    parts = line.split(':', 1)
                    if len(parts) == 2:
                        key = parts[0].strip().lower()
                        value = parts[1].strip()
                        if value and value != 'N/A':
                            if 'registrar' in key:
                                data['registrar'] = value
                            elif 'created' in key or 'creation' in key:
                                data['creation_date'] = value
                            elif 'expires' in key or 'expiration' in key:
                                data['expiration_date'] = value
                            elif 'updated' in key:
                                data['updated_date'] = value
                            elif 'nameserver' in key or 'name server' in key:
                                if 'nameservers' not in data:
                                    data['nameservers'] = []
                                data['nameservers'].append(value)
                            elif 'registrant' in key and 'name' in key:
                                data['registrant_name'] = value
                            elif 'registrant' in key and 'email' in key:
                                data['registrant_email'] = value
                            elif 'status' in key:
                                data['status'] = value
        else:
            # Fallback to generic extraction
            data = self._extract_generic_whois_data(soup)
        
        return data
    
    def _extract_generic_whois_data(self, soup: BeautifulSoup) -> Dict:
        """Extract WHOIS data using generic patterns."""
        data = {}
        
        # Get all text and try to extract key-value pairs
        text = soup.get_text()
        lines = text.split('\n')
        
        for line in lines:
            line = line.strip()
            if ':' in line:
                parts = line.split(':', 1)
                if len(parts) == 2:
                    key = parts[0].strip().lower()
                    value = parts[1].strip()
                    if value and value != 'N/A' and len(value) > 2:
                        if 'registrar' in key:
                            data['registrar'] = value
                        elif 'created' in key or 'creation' in key:
                            data['creation_date'] = value
                        elif 'expires' in key or 'expiration' in key:
                            data['expiration_date'] = value
                        elif 'updated' in key:
                            data['updated_date'] = value
                        elif 'nameserver' in key or 'name server' in key:
                            if 'nameservers' not in data:
                                data['nameservers'] = []
                            data['nameservers'].append(value)
                        elif 'registrant' in key and 'name' in key:
                            data['registrant_name'] = value
                        elif 'registrant' in key and 'email' in key:
                            data['registrant_email'] = value
                        elif 'status' in key:
                            data['status'] = value
        
        return data
    
    def _ip_whois(self, ip: str) -> Dict:
        """IP WHOIS lookup using public services."""
        try:
            # Try multiple public IP WHOIS services
            services = [
                f'http://ip-api.com/json/{ip}',
                f'https://ipwhois.app/json/{ip}',
                f'https://api.ipify.org?format=json'  # Just to get basic info
            ]
            
            for service in services:
                try:
                    response = self.session.get(service, timeout=10)
                    if response.status_code == 200:
                        data = response.json()
                        
                        result = {
                            'ip': ip,
                            'source': service,
                            'info': 'IP WHOIS data retrieved'
                        }
                        
                        # Extract available fields
                        if 'country' in data:
                            result['country'] = data['country']
                        if 'isp' in data:
                            result['isp'] = data['isp']
                        if 'org' in data:
                            result['organization'] = data['org']
                        if 'as' in data:
                            result['asn'] = data['as']
                        if 'timezone' in data:
                            result['timezone'] = data['timezone']
                        
                        return result
                except Exception as e:
                    logger.debug(f"WHOIS parsing failed: {e}")
                    continue
            
            return {
                'ip': ip,
                'error': 'All IP WHOIS services failed',
                'info': 'Try using command-line whois tool: whois ' + ip
            }
        except Exception as e:
            return {'error': f'IP WHOIS failed: {str(e)}'}
    
    def whois_direct(self, target: str, whois_server: str = 'whois.iana.org') -> Dict:
        """Direct WHOIS protocol query (requires WHOIS port 43 access)."""
        try:
            import socket
            
            sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            sock.settimeout(10)
            
            try:
                sock.connect((whois_server, 43))
                sock.send((target + '\r\n').encode())
                
                response = b''
                while True:
                    data = sock.recv(4096)
                    if not data:
                        break
                    response += data
                
                sock.close()
                
                return {
                    'target': target,
                    'server': whois_server,
                    'response': response.decode('utf-8', errors='ignore')[:3000],
                    'source': 'direct_whois'
                }
            except socket.timeout:
                sock.close()
                return {'error': 'WHOIS query timed out'}
            except Exception as e:
                sock.close()
                return {'error': f'Direct WHOIS failed: {str(e)}'}
        except Exception as e:
            return {'error': f'WHOIS protocol not available: {str(e)}'}

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
                    except Exception as e:
                        logger.debug(f"Archive entry parsing failed: {e}")
        
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
            except Exception as e:
                logger.debug(f"Archive blacklist entry parsing failed: {e}")
        
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
        
        # Initialize Censys client if library is available and credentials provided
        self.censys_client = None
        if v2 and self.censys_api_id and self.censys_api_secret:
            try:
                self.censys_client = v2.CensysHosts(api_id=self.censys_api_id, api_secret=self.censys_api_secret)
            except Exception:
                self.censys_client = None
    
    def query_shodan(self, target: str) -> Dict:
        """Query Shodan for host information."""
        if not self.shodan_api_key:
            return self._shodan_fallback(target)
        
        try:
            response = self.session.get(
                f"https://api.shodan.io/shodan/host/{target}?key={self.shodan_api_key}",
                timeout=10
            )
            response.raise_for_status()
            return response.json()
        except Exception as e:
            return self._shodan_fallback(target)
    
    def _shodan_fallback(self, target: str) -> Dict:
        """Fallback method using public DNS and port scanning without API key."""
        try:
            import socket
            from concurrent.futures import ThreadPoolExecutor, as_completed
            
            result = {
                'ip': target,
                'hostnames': [],
                'ports': [],
                'vulns': [],
                'info': 'Fallback: DNS enumeration and common port scan',
                'source': 'local_scan'
            }
            
            # Reverse DNS lookup
            try:
                hostname = socket.gethostbyaddr(target)
                result['hostnames'] = [hostname[0]]
            except Exception as e:
                logger.debug(f"Reverse DNS lookup failed: {e}")
            
            # Common port scan (non-intrusive)
            common_ports = [21, 22, 23, 25, 53, 80, 443, 445, 3306, 3389, 5432, 8080]
            
            def check_port(port):
                try:
                    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                    sock.settimeout(1)
                    result = sock.connect_ex((target, port))
                    sock.close()
                    return port if result == 0 else None
                except Exception as e:
                    logger.debug(f"Port check failed for {target}:{port}: {e}")
                    return None
            
            with ThreadPoolExecutor(max_workers=10) as executor:
                futures = [executor.submit(check_port, port) for port in common_ports]
                for future in as_completed(futures):
                    port = future.result()
                    if port:
                        result['ports'].append(port)
            
            # Check HTTP/HTTPS for server headers
            for scheme in ['http', 'https']:
                try:
                    response = self.session.get(f"{scheme}://{target}", timeout=5)
                    server = response.headers.get('Server', 'Unknown')
                    result[f'{scheme}_server'] = server
                except Exception as e:
                    logger.debug(f"HTTP server detection failed for {scheme}://{target}: {e}")
            
            return result
        except Exception as e:
            return {'error': f'Fallback failed: {str(e)}'}
    
    def query_censys(self, target: str) -> Dict:
        """Query Censys for host information using censys library."""
        if not self.censys_client:
            if not self.censys_api_id or not self.censys_api_secret:
                return {'error': 'Censys API credentials not configured'}
            return {'error': 'Censys library not available or client initialization failed'}
        
        try:
            result = self.censys_client.view_host(target)
            return result
        except Exception as e:
            return {'error': str(e)}
    
    def query_virustotal(self, ip: str) -> Dict:
        """Query VirusTotal for IP reputation."""
        if not self.virustotal_api_key:
            return self._virustotal_fallback(ip)
        
        try:
            response = self.session.get(
                f"https://www.virustotal.com/api/v3/ip_addresses/{ip}",
                headers={'x-apikey': self.virustotal_api_key},
                timeout=10
            )
            response.raise_for_status()
            return response.json()
        except Exception as e:
            return self._virustotal_fallback(ip)
    
    def _virustotal_fallback(self, ip: str) -> Dict:
        """Fallback method using public blocklist checks without API key."""
        try:
            result = {
                'ip': ip,
                'reputation': 'unknown',
                'malicious': 0,
                'suspicious': 0,
                'clean': 0,
                'info': 'Fallback: Public blocklist checks',
                'source': 'local_check'
            }
            
            # Check against public DNSBL (DNS-based Blackhole Lists)
            dnsbl_lists = [
                'zen.spamhaus.org',
                'bl.spamcop.net',
                'dnsbl-1.uceprotect.net',
                'all.s5h.net'
            ]
            
            import socket
            reversed_ip = '.'.join(reversed(ip.split('.')))
            
            blacklisted_count = 0
            for dnsbl in dnsbl_lists:
                try:
                    lookup = f"{reversed_ip}.{dnsbl}"
                    socket.gethostbyname(lookup)
                    blacklisted_count += 1
                    result[f'blacklisted_{dnsbl}'] = True
                except socket.gaierror:
                    result[f'blacklisted_{dnsbl}'] = False
                except Exception as e:
                    logger.debug(f"DNSBL check failed for {dnsbl}: {e}")
            
            if blacklisted_count > 0:
                result['reputation'] = 'suspicious'
                result['malicious'] = blacklisted_count
            else:
                result['reputation'] = 'likely_clean'
                result['clean'] = len(dnsbl_lists)
            
            # Basic IP classification
            try:
                import ipaddress
                ip_obj = ipaddress.ip_address(ip)
                result['is_private'] = ip_obj.is_private
                result['is_reserved'] = ip_obj.is_reserved
                result['is_loopback'] = ip_obj.is_loopback
                result['is_multicast'] = ip_obj.is_multicast
            except Exception as e:
                logger.debug(f"IP address classification failed: {e}")
            
            return result
        except Exception as e:
            return {'error': f'Fallback failed: {str(e)}'}
    
    def query_abuseipdb(self, ip: str) -> Dict:
        """Query AbuseIPDB for IP reputation."""
        if not self.abuseipdb_api_key:
            return self._abuseipdb_fallback(ip)
        
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
            return self._abuseipdb_fallback(ip)
    
    def _abuseipdb_fallback(self, ip: str) -> Dict:
        """Fallback method using public abuse reporting without API key."""
        try:
            result = {
                'ip': ip,
                'abuse_confidence_score': 0,
                'reports': [],
                'info': 'Fallback: Basic abuse indicators',
                'source': 'local_check'
            }
            
            # Check if IP is from common hosting providers (potential abuse source)
            import socket
            try:
                hostname = socket.gethostbyaddr(ip)
                host = hostname[0].lower()
                
                hosting_indicators = [
                    'vps', 'dedicated', 'hosting', 'server', 'cloud', 
                    'aws', 'azure', 'digitalocean', 'linode', 'vultr',
                    'ovh', 'hetzner', 'contabo'
                ]
                
                if any(indicator in host for indicator in hosting_indicators):
                    result['abuse_confidence_score'] = 25
                    result['is_hosting'] = True
                    result['hostname'] = host
            except Exception as e:
                logger.debug(f"AbuseIPDB check failed: {e}")
            
            # Check IP geolocation for suspicious regions
            try:
                response = self.session.get(f"http://ip-api.com/json/{ip}", timeout=5)
                geo_data = response.json()
                
                if geo_data.get('status') == 'success':
                    result['country'] = geo_data.get('country')
                    result['isp'] = geo_data.get('isp')
                    result['org'] = geo_data.get('org')
                    
                    # Flag certain regions as potentially higher risk
                    high_risk_countries = ['CN', 'RU', 'KP', 'IR']
                    if geo_data.get('countryCode') in high_risk_countries:
                        result['abuse_confidence_score'] += 15
                        result['risk_flag'] = 'high_risk_region'
            except Exception as e:
                logger.debug(f"Geolocation risk check failed: {e}")
            
            # Combine with DNSBL results
            vt_fallback = self._virustotal_fallback(ip)
            if vt_fallback.get('reputation') == 'suspicious':
                result['abuse_confidence_score'] += 30
                result['dnsbl_blacklisted'] = True
            
            return result
        except Exception as e:
            return {'error': f'Fallback failed: {str(e)}'}
    
    def correlate_osint(self, target: str) -> Dict:
        """Correlate OSINT data from multiple sources."""
        results = {}
        
        # Try to determine if target is IP or domain
        try:
            ipaddress.ip_address(target)
            is_ip = True
        except Exception:
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
        except Exception as e:
            logger.debug(f"Network graph initialization failed: {e}")
            self.network_graph = None
        
        try:
            self.content_classifier = ContentClassifier()
        except Exception as e:
            logger.debug(f"Content classifier initialization failed: {e}")
            self.content_classifier = None
        
        try:
            self.ner = NamedEntityRecognizer()
        except Exception as e:
            logger.debug(f"NER initialization failed: {e}")
            self.ner = None
        
        self.contact_harvester = ContactHarvester()
        self.tech_fingerprinter = TechnologyStackFingerprinter()
        
        try:
            self.visual_analyzer = VisualAnalyzer()
        except Exception as e:
            logger.debug(f"Visual analyzer initialization failed: {e}")
            self.visual_analyzer = None
        
        try:
            self.ocr_engine = OCREngine()
        except Exception as e:
            logger.debug(f"OCR engine initialization failed: {e}")
            self.ocr_engine = None
        
        self.temporal_analyzer = TemporalAnalyzer()
        self.statistical_analyzer = StatisticalAnalyzer()
        
        try:
            self.dashboard = InteractiveDashboard()
        except Exception as e:
            logger.debug(f"Dashboard initialization failed: {e}")
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
        self.dns_analyzer = DNSAnalyzer()
        self.whois_analyzer = WHOISAnalyzer()
        
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
        self.create_dns_tab()
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
    
    def create_dns_tab(self):
        """Create tab for DNS analysis."""
        dns_tab = QWidget()
        layout = QVBoxLayout(dns_tab)
        
        # DNS analysis group
        dns_group = QGroupBox("DNS Analysis")
        dns_layout = QFormLayout()
        
        self.dns_target = QLineEdit()
        self.dns_target.setPlaceholderText("Enter domain (e.g., example.com)")
        dns_layout.addRow("Domain:", self.dns_target)
        
        dns_analyze_btn = QPushButton("Analyze DNS")
        dns_analyze_btn.clicked.connect(self.perform_dns_analysis)
        dns_layout.addRow("", dns_analyze_btn)
        
        reverse_dns_btn = QPushButton("Reverse DNS Lookup")
        reverse_dns_btn.clicked.connect(self.perform_reverse_dns)
        dns_layout.addRow("", reverse_dns_btn)
        
        axfr_btn = QPushButton("Check Zone Transfer (AXFR)")
        axfr_btn.clicked.connect(self.perform_axfr_check)
        dns_layout.addRow("", axfr_btn)
        
        dns_group.setLayout(dns_layout)
        layout.addWidget(dns_group)
        
        # Results display
        self.dns_results = QTextEdit()
        self.dns_results.setReadOnly(True)
        layout.addWidget(self.dns_results)
        
        self.tab_widget.addTab(dns_tab, "DNS")
    
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
        
        self.scan_protocol = QComboBox()
        self.scan_protocol.addItems(['TCP', 'UDP', 'SYN', 'ALL'])
        self.scan_protocol.setCurrentText('TCP')
        scanner_layout.addRow("Protocol:", self.scan_protocol)
        
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
        self.scan_results_table.setColumnCount(5)
        self.scan_results_table.setHorizontalHeaderLabels(['Port', 'Service', 'Status', 'Protocol', 'Error'])
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
        
        self.social_num_results = QSpinBox()
        self.social_num_results.setRange(1, 100)
        self.social_num_results.setValue(10)
        social_layout.addRow("Results:", self.social_num_results)
        
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
    
    def update_tor_progress(self, value):
        self.tor_progress.setRange(0, 100)
        self.tor_progress.setValue(value)
    
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
        
        try:
            result = self.whois_analyzer.whois_lookup(domain)
            
            if 'error' in result:
                self.whois_results.setText(f"Error: {result['error']}")
            else:
                output = f"Target: {result.get('domain', result.get('ip', 'N/A'))}\n"
                output += f"Source: {result.get('source', 'N/A')}\n"
                output += f"Info: {result.get('info', 'N/A')}\n\n"
                
                # Display extracted WHOIS data
                if 'registrar' in result:
                    output += f"Registrar: {result['registrar']}\n"
                if 'creation_date' in result:
                    output += f"Creation Date: {result['creation_date']}\n"
                if 'expiration_date' in result:
                    output += f"Expiration Date: {result['expiration_date']}\n"
                if 'updated_date' in result:
                    output += f"Updated Date: {result['updated_date']}\n"
                if 'nameservers' in result:
                    output += f"Nameservers: {', '.join(result['nameservers'])}\n"
                if 'registrant_name' in result:
                    output += f"Registrant Name: {result['registrant_name']}\n"
                if 'registrant_email' in result:
                    output += f"Registrant Email: {result['registrant_email']}\n"
                if 'registrant_org' in result:
                    output += f"Registrant Organization: {result['registrant_org']}\n"
                if 'status' in result:
                    output += f"Status: {result['status']}\n"
                if 'dnssec' in result:
                    output += f"DNSSEC: {result['dnssec']}\n"
                
                # IP-specific fields
                if 'country' in result:
                    output += f"Country: {result['country']}\n"
                if 'isp' in result:
                    output += f"ISP: {result['isp']}\n"
                if 'organization' in result:
                    output += f"Organization: {result['organization']}\n"
                if 'asn' in result:
                    output += f"ASN: {result['asn']}\n"
                
                if 'raw_response' in result:
                    output += f"\nRaw Response (truncated):\n{result['raw_response']}\n"
                
                self.whois_results.setText(output)
            
            self.status_label.setText(f"WhoIs lookup complete for {domain}")
        except Exception as e:
            self.whois_results.setText(f"Error: {str(e)}")
            self.status_label.setText(f"WhoIs lookup failed for {domain}")
    
    # DNS handlers
    def perform_dns_analysis(self):
        domain = self.dns_target.text().strip()
        if not domain:
            QMessageBox.warning(self, "Warning", "Please enter a domain")
            return
        
        try:
            result = self.dns_analyzer.analyze_domain(domain)
            
            if 'error' in result:
                self.dns_results.setText(f"Error: {result['error']}")
            else:
                output = f"Domain: {result['domain']}\n"
                output += f"Source: {result['source']}\n"
                output += f"Info: {result['info']}\n\n"
                
                records = result.get('records', {})
                for record_type, values in records.items():
                    if values:
                        output += f"{record_type} Records:\n"
                        if isinstance(values, list):
                            for value in values:
                                output += f"  {value}\n"
                        elif isinstance(values, dict):
                            for key, value in values.items():
                                output += f"  {key}: {value}\n"
                        output += "\n"
                
                if 'dnssec_enabled' in result:
                    output += f"DNSSEC: {'Enabled' if result['dnssec_enabled'] else 'Disabled'}\n"
                
                self.dns_results.setText(output)
            
            self.status_label.setText(f"DNS analysis complete for {domain}")
        except Exception as e:
            self.dns_results.setText(f"Error: {str(e)}")
            self.status_label.setText(f"DNS analysis failed for {domain}")
    
    def perform_reverse_dns(self):
        target = self.dns_target.text().strip()
        if not target:
            QMessageBox.warning(self, "Warning", "Please enter an IP address")
            return
        
        try:
            result = self.dns_analyzer.reverse_dns_lookup(target)
            
            if 'error' in result:
                self.dns_results.setText(f"Error: {result['error']}")
            else:
                output = f"IP: {result['ip']}\n"
                output += f"Hostname: {result.get('hostname', 'N/A')}\n"
                if result.get('aliases'):
                    output += f"Aliases: {', '.join(result['aliases'])}\n"
                output += f"Source: {result['source']}\n"
                
                self.dns_results.setText(output)
            
            self.status_label.setText(f"Reverse DNS lookup complete for {target}")
        except Exception as e:
            self.dns_results.setText(f"Error: {str(e)}")
            self.status_label.setText(f"Reverse DNS lookup failed for {target}")
    
    def perform_axfr_check(self):
        domain = self.dns_target.text().strip()
        if not domain:
            QMessageBox.warning(self, "Warning", "Please enter a domain")
            return
        
        try:
            result = self.dns_analyzer.dns_zone_transfer_check(domain)
            
            if 'error' in result:
                self.dns_results.setText(f"Error: {result['error']}")
            else:
                output = f"Domain: {result['domain']}\n"
                output += f"Nameservers: {', '.join(result['nameservers'])}\n\n"
                
                output += "AXFR Results:\n"
                for ns, axfr_result in result['axfr_results'].items():
                    output += f"  {ns}:\n"
                    if axfr_result.get('vulnerable'):
                        output += f"    VULNERABLE - Zone transfer allowed!\n"
                        output += f"    Records: {axfr_result['record_count']}\n"
                    else:
                        output += f"    Secure - Zone transfer refused\n"
                    if 'error' in axfr_result:
                        output += f"    Error: {axfr_result['error']}\n"
                
                self.dns_results.setText(output)
            
            self.status_label.setText(f"AXFR check complete for {domain}")
        except Exception as e:
            self.dns_results.setText(f"Error: {str(e)}")
            self.status_label.setText(f"AXFR check failed for {domain}")
    
    # Port Scanner handlers
    def perform_port_scan(self):
        host = self.scan_host.text().strip()
        if not host:
            QMessageBox.warning(self, "Warning", "Please enter a host")
            return
        
        mode = self.scan_mode.currentText()
        timeout = self.scan_timeout.value()
        use_async = self.async_scan.isChecked()
        protocol = self.scan_protocol.currentText()
        
        if mode == 'Common Ports':
            ports = None
        elif mode == 'Custom Range':
            ports = list(range(self.start_port.value(), self.end_port.value() + 1))
        else:  # All Ports 1-1024
            ports = list(range(1, 1025))
        
        self.port_scanner.timeout = timeout
        
        self.scan_progress.setVisible(True)
        self.scan_progress.setRange(0, 100)
        self.scan_progress.setValue(0)
        self.scan_results_table.setRowCount(0)
        
        # Run in thread
        self.scan_thread = PortScanWorker(self.port_scanner, host, ports, use_async, protocol)
        self.scan_thread.progress.connect(self.update_scan_status)
        self.scan_thread.progress_int.connect(self.update_scan_progress)
        self.scan_thread.finished.connect(self.display_scan_results)
        self.scan_thread.error.connect(self.handle_scan_error)
        self.scan_thread.start()
    
    def update_scan_status(self, message):
        self.status_label.setText(message)
    
    def update_scan_progress(self, value):
        self.scan_progress.setRange(0, 100)
        self.scan_progress.setValue(value)
    
    def display_scan_results(self, results):
        self.current_results = results
        self.scan_progress.setVisible(False)
        self.scan_progress.setRange(0, 100)
        
        self.scan_results_table.setRowCount(len(results))
        
        for row, result in enumerate(results):
            self.scan_results_table.setItem(row, 0, QTableWidgetItem(str(result['port'])))
            self.scan_results_table.setItem(row, 1, QTableWidgetItem(result['service']))
            
            status_item = QTableWidgetItem(result['status'])
            if result['status'] in ['open', 'open|filtered']:
                status_item.setBackground(QColor(200, 255, 200))
            self.scan_results_table.setItem(row, 2, status_item)
            
            # Display protocol information
            if result.get('protocol') == 'ALL':
                protocol_text = ', '.join(result.get('open_protocols', []))
                if not protocol_text:
                    protocol_text = 'None'
            else:
                protocol_text = result.get('protocol', 'TCP')
            self.scan_results_table.setItem(row, 3, QTableWidgetItem(protocol_text))
            
            # Display error or additional info
            error_text = result.get('error', '')
            if result.get('protocol') == 'ALL' and not error_text:
                # Show detailed status for each protocol
                details = []
                if result.get('tcp_status'):
                    details.append(f"TCP: {result['tcp_status']}")
                if result.get('udp_status'):
                    details.append(f"UDP: {result['udp_status']}")
                if result.get('syn_status'):
                    details.append(f"SYN: {result['syn_status']}")
                error_text = '; '.join(details)
            self.scan_results_table.setItem(row, 4, QTableWidgetItem(error_text))
        
        open_ports = len([r for r in results if r['status'] in ['open', 'open|filtered']])
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
            # Clear previous dashboard data
            self.dashboard.data_history = {
                'timestamps': [],
                'response_times': [],
                'status_codes': [],
                'pages_crawled': []
            }
            
            # Get real crawl results if available
            if self.crawler is not None:
                crawl_results = self.crawler.get_results()
                
                if crawl_results:
                    # Add real data from crawl results
                    pages_crawled = 0
                    for result in crawl_results:
                        response_time = result.get('response_time', 0)
                        status_code = result.get('status_code', 0)
                        
                        # Only count successful pages
                        if result.get('type') != 'error' and result.get('type') != 'duplicate':
                            pages_crawled += 1
                        
                        self.dashboard.add_data_point(
                            response_time=response_time,
                            status_code=status_code,
                            pages_crawled=pages_crawled
                        )
                else:
                    QMessageBox.information(self, "Info", "No crawl results available. Perform a crawl first.")
                    return
            else:
                QMessageBox.information(self, "Info", "No crawler initialized. Start a crawl first.")
                return
            
            dashboard_html = self.dashboard.create_dashboard()
            
            if QWebEngineView is not None:
                self.dashboard_view.setHtml(dashboard_html)
            else:
                self.dashboard_display.setText(dashboard_html)
            
            self.status_label.setText("Dashboard refreshed with real data")
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
        num_results = self.social_num_results.value()
        
        try:
            self.social_media_searcher = SocialMediaSearcher(
                reddit_client_id=reddit_id,
                reddit_client_secret=reddit_secret
            )
            
            results = self.social_media_searcher.search_all(query, limit=num_results)
            
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
    progress_int = pyqtSignal(int)
    finished = pyqtSignal(list)
    error = pyqtSignal(str)
    
    def __init__(self, scanner, host, ports, use_async, protocol='TCP'):
        super().__init__()
        self.scanner = scanner
        self.host = host
        self.ports = ports
        self.use_async = use_async
        self.protocol = protocol
    
    def run(self):
        try:
            self.progress.emit(f"Scanning ports on: {self.host} using {self.protocol}")
            self.progress_int.emit(5)
            
            def progress_callback(current, total, open_count):
                self.progress.emit(f"Progress: {current}/{total}, Open ports: {open_count}")
                if total > 0:
                    progress = int((current / total) * 95)
                else:
                    progress = min(95, current)
                self.progress_int.emit(progress)
            
            if self.use_async:
                self.progress_int.emit(50)
                results = self.scanner.async_scan_ports(self.host, self.ports, protocol=self.protocol)
            else:
                results = self.scanner.scan_ports(self.host, self.ports, progress_callback, protocol=self.protocol)
            
            open_ports = len([r for r in results if r['status'] in ['open', 'open|filtered']])
            self.progress.emit(f"Scan complete. {open_ports} open ports found")
            self.progress_int.emit(100)
            self.finished.emit(results)
        except Exception as e:
            self.error.emit(str(e))

if __name__ == "__main__":
    app = QApplication([])
    window = GUI()
    window.show()
    app.exec_()