/**
 * Type Preview on Hover
 * Shows a preview of Agda type/function definitions when hovering over links
 */

(function() {
  // Wait for DOM to be fully loaded
  document.addEventListener('DOMContentLoaded', function() {
    // Preview container element
    const previewContainer = document.getElementById('type-preview-container');
    if (!previewContainer) {
      console.error('Type preview container not found');
      return;
    }
    
    // Delay before showing/hiding preview (ms)
    const HOVER_DELAY = 300;
    
    // Keep track of hover timers
    let showTimer = null;
    let hideTimer = null;

    // Cache for already fetched code blocks
    const codeCache = new Map();
    
    /**
     * Initialize hover events
     */
    function init() {
      // Find all hoverable links
      const hoverableLinks = document.querySelectorAll('a[data-hoverable="true"]');
      console.log('Found hoverable links:', hoverableLinks.length);
      
      // Add event listeners to each link
      hoverableLinks.forEach(link => {
        link.addEventListener('mouseenter', handleMouseEnter);
        link.addEventListener('mouseleave', handleMouseLeave);
      });
      
      // Add event listeners to the preview container
      previewContainer.addEventListener('mouseenter', () => {
        clearTimeout(hideTimer);
      });
      
      previewContainer.addEventListener('mouseleave', () => {
        hidePreview();
      });
    }
    
    /**
     * Handle mouse enter event on hoverable links
     */
    function handleMouseEnter(event) {
      const link = event.target.closest('a[data-hoverable="true"]');
      if (!link) return;
      
      // Clear any existing timers
      clearTimeout(hideTimer);
      clearTimeout(showTimer);
      
      // Set timer to show preview after delay
      showTimer = setTimeout(() => {
        const href = link.getAttribute('href');
        if (!href) return;
        
        showPreview(link, href);
      }, HOVER_DELAY);
    }
    
    /**
     * Handle mouse leave event
     */
    function handleMouseLeave() {
      clearTimeout(showTimer);
      
      // Set timer to hide preview after delay
      hideTimer = setTimeout(() => {
        hidePreview();
      }, HOVER_DELAY);
    }
    
    /**
     * Show the preview for the given link and target
     */
    async function showPreview(link, href) {
      // Parse the href to get the file and line number
      const [file, lineFragment] = href.split('#');
      
      if (!lineFragment) return;
      
      // Extract the line number from the fragment (e.g., "L42" -> 42)
      const lineNumber = parseInt(lineFragment.replace('L', ''), 10);
      if (isNaN(lineNumber)) return;
      
      // Construct cache key
      const cacheKey = `${file || window.location.pathname}#${lineNumber}`;
      
      // Check if we already have this code block in cache
      let codeBlock;
      if (codeCache.has(cacheKey)) {
        codeBlock = codeCache.get(cacheKey);
      } else {
        // Find the code block content - either in the current page or fetch from another page
        if (!file || file === window.location.pathname.split('/').pop()) {
          // Same page - look for the target line
          const targetLine = document.getElementById(`LC${lineNumber}`);
          if (!targetLine) return;
          
          // Get the containing code block
          const codeContainer = targetLine.closest('.code-content');
          if (!codeContainer) return;
          
          // Get context lines (2 before and after if available)
          const allLines = Array.from(codeContainer.querySelectorAll('.code-line'));
          const targetIndex = allLines.indexOf(targetLine);
          
          if (targetIndex === -1) return;
          
          const startIndex = Math.max(0, targetIndex - 2);
          const endIndex = Math.min(allLines.length - 1, targetIndex + 2);
          
          // Create a new container with the context lines
          const contextLines = allLines.slice(startIndex, endIndex + 1);
          
          // Get current module name from document title or path
          const moduleName = document.title || window.location.pathname.split('/').pop().replace('.html', '');
          
          // Build HTML for the code preview
          codeBlock = buildCodePreview(contextLines, lineNumber, startIndex, moduleName);
          
          // Cache the result
          codeCache.set(cacheKey, codeBlock);
        } else {
          // Different page - we'll need to fetch it
          try {
            // Extract module name from file path
            const moduleName = file.replace('.html', '');
            codeBlock = await fetchCodeFromFile(file, lineNumber, moduleName);
            if (codeBlock) {
              codeCache.set(cacheKey, codeBlock);
            }
          } catch (error) {
            console.error('Error fetching code preview:', error);
            return;
          }
        }
      }
      
      if (!codeBlock) return;
      
      // Add content to preview container
      previewContainer.innerHTML = '';
      previewContainer.appendChild(codeBlock);
      
      // Position the preview near the link
      positionPreview(link);
      
      // Show the preview
      previewContainer.style.display = 'block';
    }
    
    /**
     * Build a code preview element with the given context lines
     */
    function buildCodePreview(contextLines, highlightLineNumber, startLineIndex, moduleName = '') {
      const container = document.createElement('div');
      container.className = 'code-preview-container';
      
      // Add heading with link to full definition
      const heading = document.createElement('div');
      heading.className = 'preview-heading';
      
      // Create module name text
      const moduleText = document.createElement('span');
      moduleText.className = 'module-name';
      
      // If module name is provided, include it
      if (moduleName) {
        moduleText.textContent = `Definition in ${moduleName}`;
      } else {
        moduleText.textContent = 'Definition';
      }
      
      // Create link to full definition
      const linkToDefinition = document.createElement('a');
      linkToDefinition.className = 'link-to-definition';
      linkToDefinition.textContent = `Line ${highlightLineNumber}`;
      
      // Determine the link href
      // If this is from another file, include the file name
      if (moduleName && moduleName !== (document.title || '')) {
        linkToDefinition.href = `${moduleName}.html#L${highlightLineNumber}`;
      } else {
        linkToDefinition.href = `#L${highlightLineNumber}`;
      }
      
      // Add both elements to heading
      heading.appendChild(moduleText);
      heading.appendChild(linkToDefinition);
      
      container.appendChild(heading);
      
      // Create line numbers container
      const lineNumbers = document.createElement('div');
      lineNumbers.className = 'preview-line-numbers';
      
      // Create code content container
      const codeContent = document.createElement('div');
      codeContent.className = 'preview-code-content';
      
      // Add each line with its number
      contextLines.forEach((line, index) => {
        const actualLineNumber = startLineIndex + index + 1;
        
        // Add line number
        const lineNumberSpan = document.createElement('span');
        lineNumberSpan.className = 'preview-line-number';
        lineNumberSpan.textContent = actualLineNumber;
        if (actualLineNumber === highlightLineNumber) {
          lineNumberSpan.classList.add('highlight');
        }
        lineNumbers.appendChild(lineNumberSpan);
        
        // Add code line
        const codeLine = document.createElement('div');
        codeLine.className = 'preview-code-line';
        if (actualLineNumber === highlightLineNumber) {
          codeLine.classList.add('highlight');
        }
        
        // Clone the line content more carefully to preserve whitespace
        const lineContentWrapper = document.createElement('div');
        lineContentWrapper.style.whiteSpace = 'pre';
        lineContentWrapper.innerHTML = line.innerHTML;
        
        codeLine.appendChild(lineContentWrapper);
        codeContent.appendChild(codeLine);
      });
      
      // Create preview code structure
      const previewCode = document.createElement('div');
      previewCode.className = 'preview-code';
      previewCode.appendChild(lineNumbers);
      previewCode.appendChild(codeContent);
      
      container.appendChild(previewCode);
      return container;
    }
    
    /**
     * Fetch code from another file
     */
    async function fetchCodeFromFile(file, lineNumber, moduleName = '') {
      try {
        const response = await fetch(file);
        if (!response.ok) {
          throw new Error(`Failed to fetch ${file}: ${response.status}`);
        }
        
        const html = await response.text();
        
        // Create a temporary document to parse the HTML
        const parser = new DOMParser();
        const doc = parser.parseFromString(html, 'text/html');
        
        // Find the target line
        const targetLine = doc.getElementById(`LC${lineNumber}`);
        if (!targetLine) return null;
        
        // Get the containing code block
        const codeContainer = targetLine.closest('.code-content');
        if (!codeContainer) return null;
        
        // Get context lines (2 before and after if available)
        const allLines = Array.from(codeContainer.querySelectorAll('.code-line'));
        const targetIndex = allLines.indexOf(targetLine);
        
        if (targetIndex === -1) return null;
        
        const startIndex = Math.max(0, targetIndex - 2);
        const endIndex = Math.min(allLines.length - 1, targetIndex + 2);
        
        // Get the context lines
        const contextLines = allLines.slice(startIndex, endIndex + 1);
        
        // Build HTML for the code preview
        return buildCodePreview(contextLines, lineNumber, startIndex, moduleName);
      } catch (error) {
        console.error('Error fetching file:', error);
        return null;
      }
    }
    
    /**
     * Position the preview near the link
     */
    function positionPreview(link) {
      const linkRect = link.getBoundingClientRect();
      const scrollTop = window.pageYOffset || document.documentElement.scrollTop;
      const scrollLeft = window.pageXOffset || document.documentElement.scrollLeft;
      
      // Calculate initial position (below the link)
      let top = linkRect.bottom + scrollTop + 10;
      let left = linkRect.left + scrollLeft;
      
      // Set the position
      previewContainer.style.top = `${top}px`;
      previewContainer.style.left = `${left}px`;
      
      // After rendering, check if the preview is outside viewport
      setTimeout(() => {
        const previewRect = previewContainer.getBoundingClientRect();
        const viewportWidth = window.innerWidth;
        const viewportHeight = window.innerHeight;
        
        // Check if preview extends beyond right edge
        if (previewRect.right > viewportWidth) {
          left = Math.max(0, viewportWidth - previewRect.width - 20);
          previewContainer.style.left = `${left}px`;
        }
        
        // Check if preview extends beyond bottom edge
        if (previewRect.bottom > viewportHeight) {
          // Show above the link instead of below
          top = linkRect.top + scrollTop - previewRect.height - 10;
          previewContainer.style.top = `${top}px`;
        }
      }, 0);
    }
    
    /**
     * Hide the preview
     */
    function hidePreview() {
      previewContainer.style.display = 'none';
    }
    
    // Initialize when everything is loaded
    init();
  });
})(); 