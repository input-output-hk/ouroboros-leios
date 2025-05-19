// Client-side search functionality for Agda docs
(function() {
  // Variable declarations
  let searchActive = false;
  let searchResults = [];
  let searchIndex = {};
  
  // Create DOM elements for search
  function createSearchUI() {
    // Create overlay container
    const searchOverlay = document.createElement('div');
    searchOverlay.className = 'search-overlay';
    searchOverlay.style.display = 'none';
    
    // Create search container
    const searchContainer = document.createElement('div');
    searchContainer.className = 'search-container';
    
    // Create search input
    const searchInput = document.createElement('input');
    searchInput.type = 'text';
    searchInput.className = 'search-input';
    searchInput.placeholder = 'Search documentation...';
    searchInput.setAttribute('autocomplete', 'off');
    searchInput.setAttribute('autocorrect', 'off');
    searchInput.setAttribute('autocapitalize', 'off');
    searchInput.setAttribute('spellcheck', 'false');
    
    // Create search results container
    const resultsContainer = document.createElement('div');
    resultsContainer.className = 'search-results';
    resultsContainer.style.display = 'none'; // Initially hidden
    
    // Assemble the search UI
    searchContainer.appendChild(searchInput);
    searchContainer.appendChild(resultsContainer);
    searchOverlay.appendChild(searchContainer);
    document.body.appendChild(searchOverlay);
    
    return {
      overlay: searchOverlay,
      container: searchContainer,
      input: searchInput,
      results: resultsContainer
    };
  }
  
  // Load search index asynchronously
  function loadSearchIndex() {
    // Fetch the search index from the server
    const indexPath = window.location.pathname.includes('/formal-spec/') 
      ? '/formal-spec/search-index.json' 
      : '/search-index.json';
      
    fetch(indexPath)
      .then(response => {
        if (!response.ok) {
          throw new Error('Failed to load search index');
        }
        return response.json();
      })
      .then(data => {
        searchIndex = data;
        console.log('Search index loaded successfully');
      })
      .catch(error => {
        console.error('Error loading search index:', error);
      });
  }
  
  // Fuzzy search implementation
  function fuzzySearch(query, text) {
    if (!query || !text) return { matched: false, score: 0, highlights: [] };
    
    query = query.toLowerCase();
    text = text.toLowerCase();
    
    // For code searches, check for substring matches first
    if (text.includes(query)) {
      // Direct substring match - higher score
      const startIndex = text.indexOf(query);
      const highlights = Array.from({ length: query.length }, (_, i) => startIndex + i);
      return {
        matched: true,
        score: 10 + (query.length / text.length), // Boost direct matches
        highlights
      };
    }
    
    // Fall back to character-by-character matching
    let queryIndex = 0;
    let score = 0;
    const highlights = [];
    let lastMatchIndex = -1;
    let consecutiveMatches = 0;
    
    for (let i = 0; i < text.length; i++) {
      if (queryIndex >= query.length) break;
      
      if (text[i] === query[queryIndex]) {
        // If this is a consecutive match, increase the score
        if (lastMatchIndex === i - 1) {
          consecutiveMatches++;
          score += (consecutiveMatches * 2); // Consecutive matches are more valuable
        } else {
          consecutiveMatches = 1;
          score += 1;
        }
        
        lastMatchIndex = i;
        highlights.push(i);
        queryIndex++;
      }
    }
    
    const matched = queryIndex === query.length;
    // Normalize score based on text length (shorter matches score higher)
    const normalizedScore = matched ? score / (text.length * 0.6) : 0;
    
    return {
      matched,
      score: normalizedScore,
      highlights
    };
  }
  
  // Perform search with current query
  function performSearch(query) {
    if (!query || query.length < 2 || !searchIndex || Object.keys(searchIndex).length === 0) {
      return [];
    }
    
    const results = [];
    
    // First pass: check for exact module name matches
    for (const [moduleFile, entries] of Object.entries(searchIndex)) {
      const moduleName = moduleFile.replace('.html', '');
      
      // Search in module name
      const moduleMatch = fuzzySearch(query, moduleName);
      if (moduleMatch.matched) {
        results.push({
          type: 'module',
          moduleName: moduleName,
          url: moduleFile,
          content: moduleName,
          score: moduleMatch.score * 2, // Give more weight to module matches
          highlights: moduleMatch.highlights
        });
      }
      
      // Search in entries
      entries.forEach(entry => {
        const contentMatch = fuzzySearch(query, entry.content);
        if (contentMatch.matched) {
          results.push({
            type: entry.type,
            moduleName: moduleName,
            url: entry.lineNumber ? `${moduleFile}#L${entry.lineNumber}` : moduleFile,
            content: entry.content,
            context: entry.context || '',
            score: contentMatch.score,
            highlights: contentMatch.highlights
          });
        }
      });
    }
    
    // Sort by score (highest first)
    results.sort((a, b) => b.score - a.score);
    
    // Limit results to avoid overwhelming the UI
    return results.slice(0, 20);
  }
  
  // Render search results
  function renderSearchResults(searchUI, results, toggleSearchFn) {
    searchUI.results.innerHTML = '';
    
    if (results.length === 0) {
      const noResults = document.createElement('div');
      noResults.className = 'no-results';
      noResults.textContent = 'No results found';
      searchUI.results.appendChild(noResults);
      // Still show the container with "No results found" message
      searchUI.results.style.display = 'block';
      return;
    }
    
    // Show the results container
    searchUI.results.style.display = 'block';
    
    results.forEach((result, index) => {
      const resultEl = document.createElement('a');
      resultEl.className = 'search-result';
      resultEl.setAttribute('data-index', index);
      resultEl.href = result.url;
      
      // Handle different result types differently
      if (result.type === 'code') {
        // For code type, don't show separate title, just the context with highlights
        const preview = document.createElement('div');
        preview.className = 'result-preview code-preview';
        
        // Format and highlight code context
        if (result.context) {
          const lines = result.context.split('\n');
          let formattedContext = '';
          
          lines.forEach((line, i) => {
            // Find if this is the line containing our match
            const isMatchLine = line.toLowerCase().includes(result.content.toLowerCase());
            
            if (isMatchLine) {
              // This is the matched line, highlight the match
              formattedContext += `<span class="code-highlight">${highlightMatches(line, result.highlights)}</span>\n`;
            } else {
              // Context line
              formattedContext += `<span class="code-context">${line}</span>\n`;
            }
          });
          
          preview.innerHTML = formattedContext;
        } else {
          preview.textContent = result.content;
        }
        
        resultEl.appendChild(preview);
      } else {
        // For non-code types, show title and preview separately
        // Add result title
        const title = document.createElement('div');
        title.className = 'result-title';
        
        // Highlight matches in the title
        let titleContent = result.content;
        if (result.highlights) {
          titleContent = highlightMatches(result.content, result.highlights);
        }
        title.innerHTML = titleContent;
        resultEl.appendChild(title);
        
        // Add result preview if it exists and is different from the title
        if (result.context && result.context !== result.content) {
          const preview = document.createElement('div');
          preview.className = 'result-preview';
          
          if (result.highlights) {
            preview.innerHTML = highlightMatches(result.context, result.highlights);
          } else {
            preview.textContent = result.context;
          }
          
          resultEl.appendChild(preview);
        }
      }
      
      // Add source path and type indicator in a container
      const pathContainer = document.createElement('div');
      pathContainer.className = 'result-footer';
      
      // Add module path
      const path = document.createElement('span');
      path.className = 'result-path';
      path.textContent = result.moduleName;
      pathContainer.appendChild(path);
      
      // Add result type indicator
      const typeIndicator = document.createElement('span');
      typeIndicator.className = `result-type result-type-${result.type}`;
      typeIndicator.textContent = result.type;
      pathContainer.appendChild(typeIndicator);
      
      resultEl.appendChild(pathContainer);
      
      // Add click handler for search results - natural anchor click behavior
      resultEl.addEventListener('click', (e) => {
        e.preventDefault(); // Prevent default to handle navigation ourselves

        // Update selection highlighting visually
        const allResults = searchUI.results.querySelectorAll('.search-result');
        allResults.forEach(r => r.classList.remove('selected'));
        resultEl.classList.add('selected');
        
        // Close the search overlay
        toggleSearchFn();
        
        // Handle navigation directly without delay
        const targetUrl = result.url;
        // Handle same-page navigation specially
        const currentPath = window.location.pathname;
        const currentPathWithoutHash = currentPath.split('#')[0];
        const isInternalLink = targetUrl.startsWith('#') || 
          (targetUrl.includes('#') && targetUrl.split('#')[0] === currentPathWithoutHash);
        
        if (isInternalLink) {
          // For same-page navigation, just set the hash
          const hash = targetUrl.includes('#') ? targetUrl.split('#')[1] : targetUrl.substring(1);
          window.location.hash = hash;
        } else {
          // For different page navigation
          window.location.href = targetUrl;
        }
      });
      
      // Add hover effect manually (highlight on hover)
      resultEl.addEventListener('mouseover', () => {
        const allResults = searchUI.results.querySelectorAll('.search-result');
        allResults.forEach(r => r.classList.remove('selected'));
        resultEl.classList.add('selected');
      });
      
      searchUI.results.appendChild(resultEl);
    });
  }
  
  // Highlight matched characters in text - with consecutive matches merged
  function highlightMatches(text, highlights) {
    if (!highlights || highlights.length === 0) return text;
    
    // Sort the highlights to ensure they're in order
    highlights = [...highlights].sort((a, b) => a - b);
    
    // Identify consecutive sequences
    const sequences = [];
    let currentSequence = [highlights[0]];
    
    for (let i = 1; i < highlights.length; i++) {
      // If this highlight is consecutive with the previous one
      if (highlights[i] === highlights[i-1] + 1) {
        currentSequence.push(highlights[i]);
      } else {
        // End of a sequence
        sequences.push([...currentSequence]);
        currentSequence = [highlights[i]];
      }
    }
    
    // Add the last sequence
    if (currentSequence.length > 0) {
      sequences.push(currentSequence);
    }
    
    // Now apply the highlights in reverse order to avoid index shifting issues
    let result = text;
    
    for (let i = sequences.length - 1; i >= 0; i--) {
      const sequence = sequences[i];
      const startIdx = sequence[0];
      const endIdx = sequence[sequence.length - 1] + 1; // +1 to include the last character
      
      // Extract the substring and wrap it
      const before = result.substring(0, startIdx);
      const highlighted = result.substring(startIdx, endIdx);
      const after = result.substring(endIdx);
      
      result = before + `<span class="result-match">${highlighted}</span>` + after;
    }
    
    return result;
  }
  
  // Initialize search UI once DOM is loaded
  document.addEventListener('DOMContentLoaded', () => {
    // Load search index as soon as possible
    loadSearchIndex();
    
    // Create search UI elements
    const searchUI = createSearchUI();
    
    // Add search button to header
    const headerRight = document.querySelector('.header-right');
    if (headerRight) {
      const searchButton = document.createElement('button');
      searchButton.className = 'search-button';
      searchButton.setAttribute('title', 'Search documentation (Ctrl+K / Cmd+K)');
      searchButton.setAttribute('aria-label', 'Search documentation');
      searchButton.innerHTML = `
        <svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" width="20" height="20" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round">
          <circle cx="11" cy="11" r="8"></circle>
          <line x1="21" y1="21" x2="16.65" y2="16.65"></line>
        </svg>
      `;
      
      // Insert before theme toggle
      const themeToggle = headerRight.querySelector('.theme-toggle');
      if (themeToggle) {
        headerRight.insertBefore(searchButton, themeToggle);
      } else {
        headerRight.appendChild(searchButton);
      }
      
      // Apply consistent styling
      setTimeout(() => {
        // Match classes with other header buttons for consistent styling
        const allHeaderButtons = headerRight.querySelectorAll('button');
        allHeaderButtons.forEach(button => {
          if (!button.classList.contains('search-button')) {
            const classes = Array.from(button.classList).filter(cls => cls !== 'theme-toggle');
            searchButton.classList.add(...classes);
          }
        });
      }, 100);
      
      // Add click handler to search button
      searchButton.addEventListener('click', toggleSearch);
    }
    
    // Function to toggle search overlay
    function toggleSearch() {
      searchActive = !searchActive;
      if (searchActive) {
        searchUI.overlay.style.display = 'flex';
        searchUI.input.focus();
        searchUI.results.style.display = 'none'; // Hide results when opening
        document.body.classList.add('search-active');
      } else {
        searchUI.overlay.style.display = 'none';
        document.body.classList.remove('search-active');
        searchUI.input.value = '';
        searchUI.results.innerHTML = '';
        searchUI.results.style.display = 'none'; // Hide results when closing
      }
    }
    
    // Handle keyboard shortcuts
    document.addEventListener('keydown', (e) => {
      // Ctrl+K or Cmd+K to open search
      if ((e.ctrlKey || e.metaKey) && e.key === 'k') {
        e.preventDefault();
        toggleSearch();
      }
      
      // Escape to close search
      if (e.key === 'Escape' && searchActive) {
        e.preventDefault();
        toggleSearch();
      }
      
      // Handle arrow keys in results
      if (searchActive && searchResults.length > 0) {
        const resultElements = searchUI.results.querySelectorAll('.search-result');
        const selectedElement = searchUI.results.querySelector('.search-result.selected');
        
        if (e.key === 'ArrowDown') {
          e.preventDefault();
          let nextIndex = 0; // Default to first if none selected
          
          if (selectedElement) {
            // Find current index
            for (let i = 0; i < resultElements.length; i++) {
              if (resultElements[i] === selectedElement) {
                // Move to next (or stay at end)
                nextIndex = Math.min(i + 1, resultElements.length - 1);
                break;
              }
            }
          }
          
          // Remove selection from all
          resultElements.forEach(el => el.classList.remove('selected'));
          // Add to the next one
          resultElements[nextIndex].classList.add('selected');
          // Ensure visible
          resultElements[nextIndex].scrollIntoView({
            behavior: 'smooth',
            block: 'nearest'
          });
        } else if (e.key === 'ArrowUp') {
          e.preventDefault();
          let prevIndex = resultElements.length - 1; // Default to last if none selected
          
          if (selectedElement) {
            // Find current index
            for (let i = 0; i < resultElements.length; i++) {
              if (resultElements[i] === selectedElement) {
                // Move to previous (or stay at start)
                prevIndex = Math.max(i - 1, 0);
                break;
              }
            }
          }
          
          // Remove selection from all
          resultElements.forEach(el => el.classList.remove('selected'));
          // Add to the previous one
          resultElements[prevIndex].classList.add('selected');
          // Ensure visible
          resultElements[prevIndex].scrollIntoView({
            behavior: 'smooth',
            block: 'nearest'
          });
        } else if (e.key === 'Enter') {
          e.preventDefault();
          
          // If an item is selected, navigate to it
          if (selectedElement) {
            const index = parseInt(selectedElement.getAttribute('data-index'));
            if (!isNaN(index) && index >= 0 && index < searchResults.length) {
              // Get the result from the searchResults array
              const result = searchResults[index];
              // Close search and navigate
              toggleSearch();
              
              // Navigate directly without delay
              const targetUrl = result.url;
              // Handle same-page navigation specially
              const currentPath = window.location.pathname;
              const currentPathWithoutHash = currentPath.split('#')[0];
              const isInternalLink = targetUrl.startsWith('#') || 
                (targetUrl.includes('#') && targetUrl.split('#')[0] === currentPathWithoutHash);
              
              if (isInternalLink) {
                // For same-page navigation, just set the hash
                const hash = targetUrl.includes('#') ? targetUrl.split('#')[1] : targetUrl.substring(1);
                window.location.hash = hash;
              } else {
                // For different page navigation
                window.location.href = targetUrl;
              }
            }
          }
        }
      }
    });
    
    // Close search when clicking outside
    searchUI.overlay.addEventListener('click', (e) => {
      if (e.target === searchUI.overlay) {
        toggleSearch();
      }
    });
    
    // Prevent clicks on the container from closing the overlay
    searchUI.container.addEventListener('click', (e) => {
      e.stopPropagation();
    });
    
    // Implement search functionality with debounce
    let searchTimeout = null;
    searchUI.input.addEventListener('input', (e) => {
      const query = e.target.value.trim();
      
      // Clear previous timeout
      if (searchTimeout) {
        clearTimeout(searchTimeout);
      }
      
      // Hide results container if query is empty
      if (!query || query.length < 2) {
        searchUI.results.innerHTML = '';
        searchUI.results.style.display = 'none';
        searchResults = [];
        return;
      }
      
      // Debounce search to avoid too many searches while typing
      searchTimeout = setTimeout(() => {
        // Show loading indicator
        searchUI.results.innerHTML = '<div class="search-loading"><div class="search-loading-spinner"></div></div>';
        searchUI.results.style.display = 'block';
        
        // Perform search
        searchResults = performSearch(query);
        
        // Render results
        renderSearchResults(searchUI, searchResults, toggleSearch);
      }, 200);
    });
  });
})(); 