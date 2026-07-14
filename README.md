# Recon Tool - Advanced Web Reconnaissance Suite

## Project Overview

Webspector is a comprehensive web reconnaissance and OSINT (Open Source Intelligence) suite built with Python and PyQt5. It provides a powerful graphical interface for security researchers, penetration testers, and cybersecurity professionals to perform web crawling, search engine scraping, subdomain discovery, vulnerability scanning, and advanced OSINT correlation.

The tool integrates multiple reconnaissance techniques into a single, user-friendly application with real-time progress tracking, data visualization, and export capabilities.

---

## Key Features

### 🔍 Web Search & Scraping
- Multi-engine search support (Google, Bing, DuckDuckGo)
- Advanced search operators (site:, intitle:, inurl:, filetype:, etc.)
- Query expansion with synonyms and variations
- Multi-engine result aggregation with BM25 relevance scoring
- CAPTCHA detection and handling

### 🕷️ Web Crawling
- Recursive website crawling with configurable depth
- Async and sync crawling modes
- JavaScript rendering support (Playwright)
- Robots.txt compliance
- Polite crawling with rate limiting
- Authentication support (Basic, Bearer, Session-based)
- Content fingerprinting and near-duplicate detection
- Link extraction including AJAX and onclick events

### 🏗️ Subdomain Discovery
- DNS brute force with extensive wordlists
- Certificate Transparency log querying (crt.sh)
- Configurable concurrency and rate limiting
- Custom wordlist support

### 🔌 Port Scanning
- TCP, UDP, and SYN scanning
- Service detection with banner grabbing
- OS fingerprinting via TCP/IP heuristics
- Configurable timeout and rate limiting
- Async scanning for improved performance

### 🛡️ Vulnerability Scanning
- Exposed file detection (.git, .env, wp-config, etc.)
- Security header analysis (HSTS, CSP, X-Frame-Options, etc.)
- Admin panel discovery
- Authentication bypass testing
- SQL injection and XSS probing
- CVE vulnerability correlation

### 🌐 Network Analysis
- Network graph generation (networkx + matplotlib)
- SSL/TLS certificate analysis
- Security header validation with detailed recommendations
- Traceroute and latency measurement
- Multi-region latency analysis

### 📊 OSINT & Intelligence
- Passive OSINT correlation (Shodan, VirusTotal, AbuseIPDB, AlienVault OTX, GreyNoise)
- IP geolocation with interactive map generation (folium)
- DNS analysis (A, MX, NS, TXT, CNAME, SOA, DNSSEC)
- WHOIS lookups with fallback services
- Subdomain discovery
- Backlink discovery (CommonCrawl, Ahrefs, Majestic)
- Social media monitoring (Reddit, Mastodon)
- Knowledge graph linking (Wikidata, DBpedia, Google KG)

### 📈 Analysis & Visualization
- Content classification (sentiment analysis, topic classification)
- Named Entity Recognition (spaCy)
- Contact harvesting (emails, phones, social media handles)
- Technology stack fingerprinting with confidence scoring
- Visual analysis (screenshots, perceptual hashing, OCR)
- Temporal analysis (change detection, diff tracking)
- Statistical analysis (response times, status codes, page sizes)
- Interactive dashboards (Plotly)
- Network graph visualization

### 💾 Data Management
- Multiple export formats (JSON, CSV, HTML, TXT)
- Secure API key storage (Fernet encryption)
- Persistent configuration management
- Disk caching for large crawl results
- SQLite database storage for crawl data

---

## Installation

### Prerequisites

- Python 3.8 or higher
- pip package manager

### Basic Installation

```bash
# Clone the repository
git clone https://github.com/yourusername/recon-tool.git
cd recon-tool

# Install core dependencies
pip install requests beautifulsoup4 lxml PyQt5 aiohttp
```

### Full Installation (All Features)

```bash
# Install all dependencies
pip install -r requirements.txt
```

### Optional Dependencies

For advanced features, install optional dependencies:

```bash
# JavaScript rendering
pip install playwright
playwright install

# NLP and content analysis
pip install transformers torch spacy
python -m spacy download en_core_web_sm

# Network graph visualization
pip install networkx matplotlib

# Image analysis
pip install Pillow imagehash pytesseract

# Interactive dashboards
pip install plotly

# OSINT features
pip install python-whois dnspython geoip2 folium praw mastodon.py

# Security
pip install cryptography pyOpenSSL

# Web engine for PyQt
pip install PyQtWebEngine

# Additional utilities
pip install simhash numpy scipy
```

---

## Usage

### Launching the Application

```bash
python Recontool.pyw
```

### GUI Overview

The application is organized into multiple tabs:

#### Search Tab
- Perform web searches across multiple search engines
- Filter by site, file type, or use exact matching
- Export results in various formats

#### Crawl Tab
- Recursive website crawling with configurable depth
- Search for specific text or names in content
- Advanced options: async crawling, JavaScript rendering, authentication
- Track progress and view results in real-time

#### Advanced Search Tab
- Parse search operators (site:, intitle:, inurl:, etc.)
- Expand queries with synonyms and variations
- Generate multiple search variations automatically

#### Multi-Engine Tab
- Aggregate results from multiple search engines
- BM25 relevance scoring
- Query expansion support

#### Subdomains Tab
- DNS brute force with configurable wordlists
- Certificate Transparency log querying
- Concurrency and rate limiting controls

#### Tor/Dark Web Tab
- Crawl .onion services through Tor
- Tor connection testing

#### WhoIs Tab
- Domain and IP WHOIS lookups
- Registrar, creation date, and nameserver information

#### DNS Tab
- Comprehensive DNS analysis (A, MX, NS, TXT, CNAME, SOA)
- DNSSEC validation
- Reverse DNS lookup
- Zone transfer (AXFR) vulnerability check

#### Port Scanner Tab
- TCP, UDP, and SYN scanning
- Service detection with banner grabbing
- OS fingerprinting
- Async scanning for speed

#### Network Graph Tab
- Visualize website structure from crawl results
- Export graphs as PNG, GEXF, or GraphML
- View graph metrics (nodes, edges, centrality)

#### Content Analysis Tab
- Sentiment analysis using transformer models
- Topic classification
- Named Entity Recognition (NER)

#### Contact Harvest Tab
- Extract emails, phone numbers, social media handles
- Process HTML content and text

#### Tech Fingerprint Tab
- Detect technology stack (CMS, frameworks, web servers, analytics, etc.)
- Version detection
- Confidence scoring

#### Visual Analysis Tab
- Capture screenshots of web pages
- Perceptual hashing for phishing detection
- OCR text extraction from images

#### Temporal Analysis Tab
- Capture baselines for content comparison
- Detect changes with diff tracking
- Alert on regex pattern matches

#### Statistics Tab
- Generate statistical reports from crawl results
- Response time distribution
- Status code breakdown

#### Dashboard Tab
- Real-time interactive dashboards
- Response time charts
- Status code distribution
- Pages crawled tracking

#### IP Geolocation Tab
- Geolocate IP addresses
- Generate interactive maps

#### SSL/TLS Tab
- Certificate analysis (issuer, validity, cipher)
- Security header validation
- Detailed recommendations

#### Traceroute Tab
- TCP SYN traceroute
- Latency measurement
- Multi-region latency analysis

#### Vulnerability Scan Tab
- Exposed file detection
- Security header analysis
- Admin panel discovery
- Authentication bypass testing

#### Social Media Tab
- Reddit search (OAuth and fallback)
- Mastodon search (OAuth and fallback)

#### Backlinks Tab
- Discover backlinks via CommonCrawl
- Analyze backlink metrics

#### Passive OSINT Tab
- Shodan queries
- VirusTotal reputation checks
- AbuseIPDB checks
- AlienVault OTX queries
- GreyNoise queries

#### Knowledge Graph Tab
- Wikidata entity linking
- DBpedia queries
- Google Knowledge Graph API integration

---

## Configuration

### API Keys

The tool stores API keys securely using Fernet encryption. Keys can be configured in the respective tabs:

- **Google**: Custom Search API (for improved search results)
- **Bing**: Web Search API
- **Shodan**: Host information
- **VirusTotal**: IP reputation
- **AbuseIPDB**: Abuse reporting
- **Censys**: Host information
- **Google Knowledge Graph**: Entity linking
- **Reddit**: OAuth API (for higher rate limits)

### Configuration File

The tool creates `recontool_config.json` for persistent settings:

```json
{
  "encryption_salt": "generated_secure_salt",
  "max_threads": 10,
  "allow_localhost": false,
  "allow_private_ips": false,
  "allowed_schemes": ["http", "https"],
  "api_keys": {},
  "user_preferences": {
    "default_search_engine": "google",
    "default_num_results": 10,
    "use_async_crawling": true,
    "respect_robots_txt": true
  }
}
```

---

## Security Considerations

⚠️ **Important Security Notes**

1. **SSL/TLS Analysis**: The SSL/TLS analyzer intentionally disables hostname and certificate verification to inspect certificates. This configuration should **only** be used for analysis and **never** for secure data transmission.

2. **Port Scanning**: Port scanning can be detected and may violate terms of service. Use only on systems you own or have explicit permission to test.

3. **Vulnerability Scanning**: Automated vulnerability scanning can trigger security controls. Use responsibly and only with proper authorization.

4. **Web Crawling**: Respect robots.txt and implement rate limiting to avoid impacting target servers.

5. **API Keys**: Store API keys securely. The tool encrypts keys but consider using environment variables for sensitive credentials.

---

## Troubleshooting

### Common Issues

**Playwright not available**
```bash
playwright install
```

**spaCy model not found**
```bash
python -m spacy download en_core_web_sm
```

**PyQtWebEngine not available**
```bash
pip install PyQtWebEngine
```

**GeoIP database not found**
- Download GeoLite2 database from MaxMind
- Place in the `geoip` directory

### Logs

The tool logs to `recontool.log` for debugging purposes.

---

## Contributing

Contributions are welcome! Please follow these guidelines:

1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Run tests (if applicable)
5. Submit a pull request

---

## License

This project is licensed under the MIT License - see the LICENSE file for details.

---

## Disclaimer

This tool is intended for **educational and authorized testing purposes only**. Users are responsible for complying with all applicable laws and regulations. The developer assumes no liability for misuse of this tool.

---

## Acknowledgments

- BeautifulSoup4 - HTML parsing
- PyQt5 - GUI framework
- Playwright - JavaScript rendering
- spaCy - Natural Language Processing
- networkx - Graph analysis
- transformers - NLP models
- dnspython - DNS queries
- geoip2 - IP geolocation
- OpenCV - Image processing
- Various OSINT services and APIs

---

## Version History

- **v2.0** - Complete rewrite with PyQt5 GUI
- **v1.0** - Initial CLI version

---

## Quick Start Example

```python
# Command-line usage example (if you want to use the modules programmatically)
from recontool import Crawler, Searcher, Exporter

# Search example
searcher = Searcher()
results = searcher.search("example.com", engine="google", num_results=10)

# Crawl example
crawler = Crawler("https://example.com", depth=2)
crawl_results = crawler.crawl(search_text=["admin", "login"])

# Export results
exporter = Exporter()
exporter.export(crawl_results, "output.json", "json")
```
