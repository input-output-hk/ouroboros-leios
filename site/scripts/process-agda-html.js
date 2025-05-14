const fs = require('fs');
const path = require('path');

const AGDA_HTML_DIR = path.join(__dirname, '../static/agda_html');

// First, collect all module information and create search index
const modules = new Map();
const moduleGroups = new Map();
const searchIndex = [];

fs.readdirSync(AGDA_HTML_DIR).forEach(file => {
    if (file.endsWith('.html')) {
        const filePath = path.join(AGDA_HTML_DIR, file);
        const content = fs.readFileSync(filePath, 'utf8');
        // Look for both h1 and title tags to find module names
        const h1Match = content.match(/<h1[^>]*>([^<]+)<\/h1>/);
        const titleMatch = content.match(/<title[^>]*>([^<]+)<\/title>/);
        const moduleName = h1Match ? h1Match[1].trim() : (titleMatch ? titleMatch[1].trim() : file);
        
        // Only include Leios package modules
        if (moduleName.startsWith('Leios.') || 
            moduleName.startsWith('Ouroboros.') ||
            moduleName.startsWith('Cardano.')) {
            
            // Get the top-level module name for grouping
            const topLevel = moduleName.split('.')[0];
            if (!moduleGroups.has(topLevel)) {
                moduleGroups.set(topLevel, []);
            }
            
            const moduleInfo = {
                name: moduleName,
                path: file,
                group: topLevel
            };
            
            modules.set(file, moduleInfo);
            moduleGroups.get(topLevel).push(moduleInfo);
            
            // Add to search index
            const lines = content.split('\n');
            lines.forEach((line, index) => {
                if (line.trim()) {  // Only index non-empty lines
                    // Strip HTML tags from the line
                    const cleanLine = line.replace(/<[^>]*>/g, ' ').replace(/\s+/g, ' ').trim();
                    if (cleanLine) {
                        // Try to extract the type/expression from the line
                        const typeMatch = cleanLine.match(/^([^:]+):/);
                        const expressionMatch = cleanLine.match(/^([^=]+)=/);
                        const title = typeMatch ? typeMatch[1].trim() : 
                                    expressionMatch ? expressionMatch[1].trim() : 
                                    cleanLine.trim();
                        
                        searchIndex.push({
                            moduleName: moduleName,
                            path: file,
                            group: topLevel,
                            lineNumber: index + 1,
                            title: title,
                            content: cleanLine,
                            searchableContent: cleanLine.toLowerCase()
                        });
                    }
                }
            });
        }
    }
});

// Create the script file
const scriptContent = `
// Search functionality
const searchIndex = ${JSON.stringify(searchIndex)};
const searchInput = document.querySelector('.search-input');
const searchResults = document.querySelector('.search-results');
const searchOverlay = document.querySelector('.search-overlay');

function toggleSearch() {
  searchOverlay.classList.toggle('active');
  if (searchOverlay.classList.contains('active')) {
    searchInput.focus();
  }
}

if (searchInput && searchResults) {
  // Update the search results HTML generation
  function generateSearchResults(results) {
    return results.map(result => {
      // The content is already clean (no HTML tags)
      const highlightedContent = result.content.replace(
        new RegExp(result.term, 'gi'),
        match => '<span class="search-match">' + match + '</span>'
      );
      
      // Ensure the path is properly encoded
      const encodedPath = encodeURIComponent(result.path);
      
      return '<a href="/agda_html/' + encodedPath + '#L' + result.lineNumber + '" class="search-result" data-line="' + result.lineNumber + '" data-term="' + result.term + '">' +
             '<span class="result-match">' + highlightedContent + '</span>' +
             '<span class="result-file">' + result.moduleName + '</span>' +
             '</a>';
    }).join('');
  }

  searchInput.addEventListener('input', (e) => {
    const query = e.target.value.toLowerCase();
    if (query.length < 2) {
      searchResults.innerHTML = '';
      return;
    }

    const results = searchIndex
      .filter(item => item.searchableContent.includes(query))
      .map(item => ({
        ...item,
        term: query
      }));

    if (results.length > 0) {
      searchResults.innerHTML = generateSearchResults(results);
    } else {
      searchResults.innerHTML = '<div class="search-no-results">No results found</div>';
    }
  });

  // Add scroll-to-line functionality
  document.addEventListener('click', (e) => {
    const result = e.target.closest('.search-result');
    if (result) {
      e.preventDefault(); // Prevent default link behavior
      const lineNumber = result.dataset.line;
      const searchTerm = result.dataset.term;
      const href = result.getAttribute('href');
      
      // If we're already on the target page
      if (window.location.pathname.endsWith(href.split('#')[0])) {
        scrollToLine(lineNumber, searchTerm);
      } else {
        // If we're not on the target page, navigate to it
        // Store the line number and search term in sessionStorage
        sessionStorage.setItem('scrollToLine', lineNumber);
        sessionStorage.setItem('searchTerm', searchTerm);
        window.location.href = href;
      }
      
      searchOverlay.classList.remove('active');
      searchInput.value = ''; // Clear the search input
      searchResults.innerHTML = ''; // Clear the results
    }
  });

  // Function to scroll to a specific line and highlight terms
  function scrollToLine(lineNumber, searchTerm) {
    // Wait for the next frame to ensure content is rendered
    requestAnimationFrame(() => {
      const targetElement = document.querySelector('#L' + lineNumber);
      if (targetElement) {
        // Add a small delay to ensure content is fully rendered
        setTimeout(() => {
          targetElement.scrollIntoView({ behavior: 'smooth', block: 'center' });
          targetElement.classList.add('highlight-line');
          setTimeout(() => targetElement.classList.remove('highlight-line'), 2000);
          
          // Highlight all matching terms on the page
          const content = document.querySelector('.agda-content');
          if (content && searchTerm) {
            const regex = new RegExp(searchTerm, 'gi');
            const walker = document.createTreeWalker(content, NodeFilter.SHOW_TEXT, null, false);
            const nodesToHighlight = [];
            
            while (walker.nextNode()) {
              const node = walker.currentNode;
              if (node.textContent.match(regex)) {
                nodesToHighlight.push(node);
              }
            }
            
            nodesToHighlight.forEach(node => {
              const span = document.createElement('span');
              span.className = 'search-term-highlight';
              span.innerHTML = node.textContent.replace(regex, match => '<mark>' + match + '</mark>');
              node.parentNode.replaceChild(span, node);
            });
            
            // Remove highlights after 5 seconds
            setTimeout(() => {
              const highlights = document.querySelectorAll('.search-term-highlight');
              highlights.forEach(highlight => {
                const text = highlight.textContent;
                const textNode = document.createTextNode(text);
                highlight.parentNode.replaceChild(textNode, highlight);
              });
            }, 5000);
          }
        }, 100); // Small delay to ensure content is rendered
      }
    });
  }

  // Check for stored line number and search term on page load
  window.addEventListener('load', () => {
    // Wait for a short time to ensure all content is loaded and rendered
    setTimeout(() => {
      const storedLine = sessionStorage.getItem('scrollToLine');
      const storedTerm = sessionStorage.getItem('searchTerm');
      if (storedLine) {
        scrollToLine(storedLine, storedTerm);
        // Clear the stored values
        sessionStorage.removeItem('scrollToLine');
        sessionStorage.removeItem('searchTerm');
      }
    }, 100);
  });

  // Close search when clicking outside or pressing Escape
  document.addEventListener('click', (e) => {
    if (e.target === searchOverlay) {
      searchOverlay.classList.remove('active');
    }
  });

  document.addEventListener('keydown', (e) => {
    if (e.key === 'Escape' && searchOverlay.classList.contains('active')) {
      searchOverlay.classList.remove('active');
    }
  });
}

// Theme toggle functionality
function toggleTheme() {
  const html = document.documentElement;
  const currentTheme = html.getAttribute('data-theme');
  const newTheme = currentTheme === 'dark' ? 'light' : 'dark';
  html.setAttribute('data-theme', newTheme);
  localStorage.setItem('theme', newTheme);
}

// Initialize theme from localStorage or system preference
const savedTheme = localStorage.getItem('theme');
if (savedTheme) {
  document.documentElement.setAttribute('data-theme', savedTheme);
} else if (window.matchMedia('(prefers-color-scheme: dark)').matches) {
  document.documentElement.setAttribute('data-theme', 'dark');
}
`;

fs.writeFileSync(path.join(AGDA_HTML_DIR, 'agda.js'), scriptContent);

// Process all HTML files in the agda_html directory
fs.readdirSync(AGDA_HTML_DIR).forEach(file => {
    if (file.endsWith('.html')) {
        const filePath = path.join(AGDA_HTML_DIR, file);
        let content = fs.readFileSync(filePath, 'utf8');

        // Add our custom CSS and theme toggle
        content = content.replace(
            /<link rel="stylesheet" href="Agda.css">/,
            `<link rel="stylesheet" href="Agda.css">
             <link rel="stylesheet" href="agda.css">
             <link href="https://fonts.googleapis.com/css2?family=Fira+Code:wght@400;500&display=swap" rel="stylesheet">`
        );

        // Add header, sidebar, and theme toggle
        content = content.replace(
            /<body[^>]*>/,
            `<body>
             <div class="agda-header">
               <div class="agda-header-left">
                 <a href="/formal-spec/">Back</a>
                 <button class="search-button" onclick="toggleSearch()">
                   <svg viewBox="0 0 24 24" width="24" height="24">
                     <path fill="currentColor" d="M15.5 14h-.79l-.28-.27C15.41 12.59 16 11.11 16 9.5 16 5.91 13.09 3 9.5 3S3 5.91 3 9.5 5.91 16 9.5 16c1.61 0 3.09-.59 4.23-1.57l.27.28v.79l5 4.99L20.49 19l-4.99-5zm-6 0C7.01 14 5 11.99 5 9.5S7.01 5 9.5 5 14 7.01 14 9.5 11.99 14 9.5 14z"/>
                   </svg>
                   Search...
                 </button>
               </div>
               <div class="agda-header-right">
                 <a href="https://github.com/input-output-hk/ouroboros-leios-formal-spec" class="github-link" target="_blank" rel="noopener noreferrer" title="View on GitHub">
                   <svg viewBox="0 0 24 24" width="24" height="24">
                     <path fill="currentColor" d="M12 0c-6.626 0-12 5.373-12 12 0 5.302 3.438 9.8 8.207 11.387.599.111.793-.261.793-.577v-2.234c-3.338.726-4.033-1.416-4.033-1.416-.546-1.387-1.333-1.756-1.333-1.756-1.089-.745.083-.729.083-.729 1.205.084 1.839 1.237 1.839 1.237 1.07 1.834 2.807 1.304 3.492.997.107-.775.418-1.305.762-1.604-2.665-.305-5.467-1.334-5.467-5.931 0-1.311.469-2.381 1.236-3.221-.124-.303-.535-1.524.117-3.176 0 0 1.008-.322 3.301 1.23.957-.266 1.983-.399 3.003-.404 1.02.005 2.047.138 3.006.404 2.291-1.552 3.297-1.23 3.297-1.23.653 1.653.242 2.874.118 3.176.77.84 1.235 1.911 1.235 3.221 0 4.609-2.807 5.624-5.479 5.921.43.372.823 1.102.823 2.222v3.293c0 .319.192.694.801.576 4.765-1.589 8.199-6.086 8.199-11.386 0-6.627-5.373-12-12-12z"/>
                   </svg>
                 </a>
                 <button class="theme-toggle" onclick="toggleTheme()" title="Toggle theme">
                   <span class="light-icon">
                     <svg viewBox="0 0 24 24" width="24" height="24">
                       <path fill="currentColor" d="M12,9c1.65,0,3,1.35,3,3s-1.35,3-3,3s-3-1.35-3-3S10.35,9,12,9 M12,7c-2.76,0-5,2.24-5,5s2.24,5,5,5s5-2.24,5-5 S14.76,7,12,7L12,7z M2,13l2,0c0.55,0,1-0.45,1-1s-0.45-1-1-1l-2,0c-0.55,0-1,0.45-1,1S1.45,13,2,13z M20,13l2,0c0.55,0,1-0.45,1-1 s-0.45-1-1-1l-2,0c-0.55,0-1,0.45-1,1S19.45,13,20,13z M11,2v2c0,0.55,0.45,1,1,1s1-0.45,1-1V2c0-0.55-0.45-1-1-1S11,1.45,11,2z M11,20v2c0,0.55,0.45,1,1,1s1-0.45,1-1v-2c0-0.55-0.45-1-1-1C11.45,19,11,19.45,11,20z M5.99,4.58c-0.39-0.39-1.03-0.39-1.41,0 c-0.39,0.39-0.39,1.03,0,1.41l1.06,1.06c0.39,0.39,1.03,0.39,1.41,0s0.39-1.03,0-1.41L5.99,4.58z M18.36,16.95 c-0.39-0.39-1.03-0.39-1.41,0c-0.39,0.39-0.39,1.03,0,1.41l1.06,1.06c0.39,0.39,1.03,0.39,1.41,0c0.39-0.39,0.39-1.03,0-1.41 L18.36,16.95z M19.42,5.99c0.39-0.39,0.39-1.03,0-1.41c-0.39-0.39-1.03-0.39-1.41,0l-1.06,1.06c-0.39,0.39-0.39,1.03,0,1.41 s1.03,0.39,1.41,0L19.42,5.99z M7.05,18.36c0.39-0.39,0.39-1.03,0-1.41c-0.39-0.39-1.03-0.39-1.41,0l-1.06,1.06 c-0.39,0.39-0.39,1.03,0,1.41s1.03,0.39,1.41,0L7.05,18.36z"></path>
                     </svg>
                   </span>
                   <span class="dark-icon">
                     <svg viewBox="0 0 24 24" width="24" height="24">
                       <path fill="currentColor" d="M9.37,5.51C9.19,6.15,9.1,6.82,9.1,7.5c0,4.08,3.32,7.4,7.4,7.4c0.68,0,1.35-0.09,1.99-0.27C17.45,17.19,14.93,19,12,19 c-3.86,0-7-3.14-7-7C5,9.07,6.81,6.55,9.37,5.51z M12,3c-4.97,0-9,4.03-9,9s4.03,9,9,9s9-4.03,9-9c0-0.46-0.04-0.92-0.1-1.36 c-0.98,1.37-2.58,2.26-4.4,2.26c-2.98,0-5.4-2.42-5.4-5.4c0-1.81,0.89-3.42,2.26-4.4C12.92,3.04,12.46,3,12,3L12,3z"></path>
                     </svg>
                   </span>
                 </button>
               </div>
             </div>
             <div class="search-overlay">
               <div class="search-modal">
                 <div class="search-container">
                   <input type="text" class="search-input" placeholder="Search modules..." />
                   <div class="search-results"></div>
                 </div>
               </div>
             </div>
             <div class="agda-container">
               <nav class="agda-sidebar">
                 <h3>Modules</h3>
                 ${Array.from(moduleGroups.entries())
                   .sort(([a], [b]) => a.localeCompare(b))
                   .map(([group, modules]) => `
                     <h4>${group}</h4>
                     <ul>
                       ${modules
                         .sort((a, b) => a.name.localeCompare(b.name))
                         .map(m => `<li><a href="/agda_html/${m.path}" ${m.path === file ? 'class="active"' : ''}>${m.name.replace(`${group}.`, '')}</a></li>`)
                         .join('\n')}
                     </ul>
                   `).join('\n')}
               </nav>
               <main class="agda-content">
             <script src="agda.js"></script>`
        );

        // Close the main content div
        content = content.replace(
            /<\/body>/,
            `</main></div></body>`
        );

        // Fix internal links
        content = content.replace(
            /href="([^"]*\.html)(#[^"]*)?"/g,
            (match, file, anchor) => {
                if (file.startsWith('http')) {
                    return match; // Keep external links as is
                }
                // Remove any existing /agda_html/ prefix to prevent duplication
                const cleanFile = file.replace(/^\/?agda_html\//, '');
                return `href="/agda_html/${cleanFile}${anchor || ''}"`;
            }
        );

        // Update the theme toggle button HTML
        content = content.replace(
            /<button class="theme-toggle"[^>]*>.*?<\/button>/,
            `<button class="theme-toggle" onclick="toggleTheme()" title="Toggle theme">
              <span class="light-icon">
                <svg viewBox="0 0 24 24" width="24" height="24">
                  <path fill="currentColor" d="M12,9c1.65,0,3,1.35,3,3s-1.35,3-3,3s-3-1.35-3-3S10.35,9,12,9 M12,7c-2.76,0-5,2.24-5,5s2.24,5,5,5s5-2.24,5-5 S14.76,7,12,7L12,7z M2,13l2,0c0.55,0,1-0.45,1-1s-0.45-1-1-1l-2,0c-0.55,0-1,0.45-1,1S1.45,13,2,13z M20,13l2,0c0.55,0,1-0.45,1-1 s-0.45-1-1-1l-2,0c-0.55,0-1,0.45-1,1S19.45,13,20,13z M11,2v2c0,0.55,0.45,1,1,1s1-0.45,1-1V2c0-0.55-0.45-1-1-1S11,1.45,11,2z M11,20v2c0,0.55,0.45,1,1,1s1-0.45,1-1v-2c0-0.55-0.45-1-1-1C11.45,19,11,19.45,11,20z M5.99,4.58c-0.39-0.39-1.03-0.39-1.41,0 c-0.39,0.39-0.39,1.03,0,1.41l1.06,1.06c0.39,0.39,1.03,0.39,1.41,0s0.39-1.03,0-1.41L5.99,4.58z M18.36,16.95 c-0.39-0.39-1.03-0.39-1.41,0c-0.39,0.39-0.39,1.03,0,1.41l1.06,1.06c0.39,0.39,1.03,0.39,1.41,0c0.39-0.39,0.39-1.03,0-1.41 L18.36,16.95z M19.42,5.99c0.39-0.39,0.39-1.03,0-1.41c-0.39-0.39-1.03-0.39-1.41,0l-1.06,1.06c-0.39,0.39-0.39,1.03,0,1.41 s1.03,0.39,1.41,0L19.42,5.99z M7.05,18.36c0.39-0.39,0.39-1.03,0-1.41c-0.39-0.39-1.03-0.39-1.41,0l-1.06,1.06 c-0.39,0.39-0.39,1.03,0,1.41s1.03,0.39,1.41,0L7.05,18.36z"></path>
                     </svg>
                   </span>
                   <span class="dark-icon">
                     <svg viewBox="0 0 24 24" width="24" height="24">
                       <path fill="currentColor" d="M9.37,5.51C9.19,6.15,9.1,6.82,9.1,7.5c0,4.08,3.32,7.4,7.4,7.4c0.68,0,1.35-0.09,1.99-0.27C17.45,17.19,14.93,19,12,19 c-3.86,0-7-3.14-7-7C5,9.07,6.81,6.55,9.37,5.51z M12,3c-4.97,0-9,4.03-9,9s4.03,9,9,9s9-4.03,9-9c0-0.46-0.04-0.92-0.1-1.36 c-0.98,1.37-2.58,2.26-4.4,2.26c-2.98,0-5.4-2.42-5.4-5.4c0-1.81,0.89-3.42,2.26-4.4C12.92,3.04,12.46,3,12,3L12,3z"></path>
                     </svg>
                   </span>
                 </button>`
        );

        // Write the processed file
        fs.writeFileSync(filePath, content);
        console.log(`Processed ${file}`);
    }
});

console.log('Finished processing Agda HTML files');

// Update the module list to ensure all modules are properly linked
const AGDA_MODULES = [
  { 
    name: 'Leios.Base',
    path: 'Leios.Base.html',
    description: 'Core definitions and types'
  },
  { 
    name: 'Leios.Voting',
    path: 'Leios.Voting.html',
    description: 'Voting mechanism and rules'
  },
  { 
    name: 'Leios.Protocol',
    path: 'Leios.Protocol.html',
    description: 'Protocol state and transitions'
  },
  { 
    name: 'Leios.Blocks',
    path: 'Leios.Blocks.html',
    description: 'Block structure and validation'
  },
  { 
    name: 'Leios.Network',
    path: 'Leios.Network.html',
    description: 'Network communication and messages'
  },
  { 
    name: 'Leios.Chain',
    path: 'Leios.Chain.html',
    description: 'Chain state and updates'
  },
  { 
    name: 'Leios.Validation',
    path: 'Leios.Validation.html',
    description: 'Transaction and block validation'
  },
  { 
    name: 'Leios.Properties',
    path: 'Leios.Properties.html',
    description: 'Protocol properties and proofs'
  }
]; 