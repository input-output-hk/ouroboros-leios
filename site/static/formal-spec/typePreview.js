/**
 * Type Preview on Hover
 * Shows a preview of Agda type/function definitions when hovering over links
 */

(function() {
  let previewContainer;
  let activeTimeout;
  let activeLink = null;
  const codeCache = new Map();
  const previewDelay = 300; // ms delay before showing preview
  
  document.addEventListener('DOMContentLoaded', function() {
    init();
  });
  
  /**
   * Initialize the preview functionality
   */
  function init() {
    // Get or create the preview container
    previewContainer = document.getElementById('type-preview-container');
    if (!previewContainer) {
      previewContainer = document.createElement('div');
      previewContainer.id = 'type-preview-container';
      previewContainer.className = 'type-preview-container';
      previewContainer.style.display = 'none';
      document.body.appendChild(previewContainer);
    }
    
    // Add event listeners to hoverable links
    function setupHoverableLinks() {
      const hoverableLinks = document.querySelectorAll('.type-hoverable');
      hoverableLinks.forEach(link => {
        link.addEventListener('mouseenter', handleMouseEnter);
        link.addEventListener('mouseleave', handleMouseLeave);
        link.addEventListener('focus', handleMouseEnter);
        link.addEventListener('blur', handleMouseLeave);
      });
    }
    
    // Initial setup
    setupHoverableLinks();
    
    // Hide preview when clicking outside
    document.addEventListener('click', function(event) {
      if (previewContainer.style.display === 'block' && 
          !previewContainer.contains(event.target) && 
          !activeLink?.contains(event.target)) {
        hidePreview();
      }
    });
  }
  
  /**
   * Handle mouse enter event on hoverable links
   */
  function handleMouseEnter(event) {
    // Clear any existing timeout
    if (activeTimeout) {
      clearTimeout(activeTimeout);
    }
    
    // Set the active link
    activeLink = event.target;
    
    // Get the href attribute or data-original-href if available
    const originalHref = activeLink.getAttribute('data-original-href');
    const href = activeLink.getAttribute('href');
    
    if (!href) return;
    
    // Use timeout to avoid showing preview for quick mouse movements
    activeTimeout = setTimeout(() => {
      showPreview(activeLink, href);
    }, previewDelay);
  }
  
  /**
   * Handle mouse leave event
   */
  function handleMouseLeave() {
    // Clear timeout if mouse leaves quickly
    if (activeTimeout) {
      clearTimeout(activeTimeout);
      activeTimeout = null;
    }
  }
  
  /**
   * Determine which context lines to include in the preview
   */
  function determineContextLines(allLines, targetIndex) {
    // Default to showing a few lines before and after the target line
    const defaultContextLines = 3;
    
    // Helper function to check if a line is empty or just whitespace
    const isEmptyLine = (line) => {
      const content = line.textContent || '';
      return content.trim() === '';
    };
    
    // Helper function to check if a line contains a comment
    const isComment = (line) => {
      const content = line.innerHTML || '';
      return content.includes('class="Comment"');
    };

    // Helper function to extract comment text from a line
    const extractCommentText = (line) => {
      const commentElements = line.querySelectorAll('.Comment');
      if (commentElements.length === 0) return '';
      
      // Join all comment text and clean it up
      return Array.from(commentElements)
        .map(el => el.textContent || '')
        .join(' ')
        .trim();
    };
    
    // Start with basic context
    let startIndex = Math.max(0, targetIndex - defaultContextLines);
    let endIndex = Math.min(allLines.length - 1, targetIndex + defaultContextLines);
    
    // Look for comments that precede the definition
    let commentLines = [];
    let definitionStartIndex = targetIndex;
    
    // Look backward from the target to find comments and the start of the definition
    let idx = targetIndex;
    while (idx > 0) {
      idx--;
      
      // If we find an empty line, check what's before it
      if (isEmptyLine(allLines[idx])) {
        // Look further back to see if there are comments before this empty line
        let commentIdx = idx - 1;
        let foundComments = [];
        
        while (commentIdx >= 0 && (isComment(allLines[commentIdx]) || isEmptyLine(allLines[commentIdx]))) {
          if (isComment(allLines[commentIdx])) {
            foundComments.unshift({
              line: allLines[commentIdx],
              text: extractCommentText(allLines[commentIdx])
            });
          }
          commentIdx--;
        }
        
        if (foundComments.length > 0) {
          commentLines = foundComments;
        }
        
        // The definition starts after the empty line
        definitionStartIndex = idx + 1;
        break;
      }
      
      // If we find a comment line directly before the definition
      if (isComment(allLines[idx])) {
        // Collect all consecutive comment lines
        let commentIdx = idx;
        let foundComments = [];
        
        while (commentIdx >= 0 && (isComment(allLines[commentIdx]) || isEmptyLine(allLines[commentIdx]))) {
          if (isComment(allLines[commentIdx])) {
            foundComments.unshift({
              line: allLines[commentIdx],
              text: extractCommentText(allLines[commentIdx])
            });
          }
          commentIdx--;
        }
        
        if (foundComments.length > 0) {
          commentLines = foundComments;
        }
        
        // The definition starts AFTER the comment lines
        // Find the first non-comment, non-empty line after the comments
        let nextIdx = idx;
        while (nextIdx < allLines.length && (isComment(allLines[nextIdx]) || isEmptyLine(allLines[nextIdx]))) {
          nextIdx++;
        }
        definitionStartIndex = nextIdx;
        break;
      }
      
      definitionStartIndex = idx;
    }
    
    // Set the start index to the beginning of the definition (excluding comments)
    startIndex = definitionStartIndex;
    
    // Look forward to capture the entire declaration
    idx = targetIndex;
    let bracketCount = 0;
    let foundEndOfDeclaration = false;
    
    // Count open and close brackets/parens to find the complete expression
    while (idx < allLines.length - 1 && !foundEndOfDeclaration) {
      const content = allLines[idx].textContent || '';
      
      // Count brackets crudely (this is a simple heuristic)
      for (const char of content) {
        if (char === '(' || char === '{' || char === '[') bracketCount++;
        if (char === ')' || char === '}' || char === ']') bracketCount--;
      }
      
      idx++;
      
      // Check if the next line is empty and brackets are balanced
      if (idx < allLines.length && bracketCount <= 0) {
        if (isEmptyLine(allLines[idx]) || isComment(allLines[idx])) {
          // Found the end, but don't include this empty line
          foundEndOfDeclaration = true;
          // Keep endIndex at the last non-empty line
          endIndex = idx - 1;
          break;
        }
      }
      
      // If we reached here, include this line
      endIndex = idx;
    }
    
    // Ensure we don't exceed array bounds
    startIndex = Math.max(0, startIndex);
    endIndex = Math.min(allLines.length - 1, endIndex);
    
    return { startIndex, endIndex, commentLines };
  }
  
  /**
   * Show the preview for the given link and target
   */
  async function showPreview(link, href) {
    // Parse the href to get the file and line number
    const [file, lineFragment] = href.split('#');
    
    if (!lineFragment) return;
    
    // Extract the line number and block ID from the fragment
    let lineNumber, blockId;
    
    // Check if using the new block-specific format (BX-LY)
    const blockLineMatch = lineFragment.match(/^(B\d+)-L(\d+)$/);
    if (blockLineMatch) {
      blockId = blockLineMatch[1];
      lineNumber = parseInt(blockLineMatch[2], 10);
    } else if (lineFragment.startsWith('L')) {
      // Legacy format (LY)
      blockId = 'B1'; // Assume first block for legacy format
      lineNumber = parseInt(lineFragment.substring(1), 10);
    } else {
      return; // Unknown format
    }
    
    if (isNaN(lineNumber)) return;
    
    // Construct cache key
    const cacheKey = `${file || window.location.pathname}#${blockId}-${lineNumber}`;
    
    // Check if we already have this code block in cache
    let codeBlock;
    if (codeCache.has(cacheKey)) {
      codeBlock = codeCache.get(cacheKey);
    } else {
      // Find the code block content - either in the current page or fetch from another page
      if (!file || file === window.location.pathname.split('/').pop()) {
        // Same page - look for the target line
        const lineContentId = `${blockId}-LC${lineNumber}`;
        const targetLine = document.getElementById(lineContentId);
        if (!targetLine) return;
        
        // Get the containing code block
        const codeContainer = targetLine.closest('.code-content');
        if (!codeContainer) return;
        
        // Get all lines from the code container
        const allLines = Array.from(codeContainer.querySelectorAll('.code-line'));
        const targetIndex = allLines.indexOf(targetLine);
        
        if (targetIndex === -1) return;
        
        // Determine context-aware start and end indexes
        const { startIndex, endIndex, commentLines } = determineContextLines(allLines, targetIndex);
        
        // Create a new container with the context lines
        const contextLines = allLines.slice(startIndex, endIndex + 1);
        
        // Get current module name from document title or path
        const moduleName = document.title || window.location.pathname.split('/').pop().replace('.html', '');
        
        // Build HTML for the code preview
        codeBlock = buildCodePreview(contextLines, lineNumber, startIndex, moduleName, blockId, commentLines);
        
        // Cache the result
        codeCache.set(cacheKey, codeBlock);
      } else {
        // Different page - we'll need to fetch it
        try {
          // Extract module name from file path
          const moduleName = file.replace('.html', '');
          codeBlock = await fetchCodeFromFile(file, lineNumber, moduleName, blockId);
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
  function buildCodePreview(contextLines, highlightLineNumber, startLineIndex, moduleName = '', blockId = 'B1', commentLines = []) {
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
    
    // Determine the link href using block-specific format
    // If this is from another file, include the file name
    if (moduleName && moduleName !== (document.title || '')) {
      linkToDefinition.href = `${moduleName}.html#${blockId}-L${highlightLineNumber}`;
    } else {
      linkToDefinition.href = `#${blockId}-L${highlightLineNumber}`;
    }
    
    // Add both elements to heading
    heading.appendChild(moduleText);
    heading.appendChild(linkToDefinition);
    
    container.appendChild(heading);
    
    // Add comment section if we have comments
    if (commentLines.length > 0) {
      const commentContainer = document.createElement('div');
      commentContainer.className = 'preview-comment-container';
      
      // Combine all comment text into one block for proper list processing
      let allCommentText = '';
      commentLines.forEach((comment, index) => {
        const commentText = comment.text;
        
        // Clean up the comment text - remove comment delimiters and extra whitespace
        let cleanText = commentText
          .replace(/^\{-\s*/, '')  // Remove opening {-
          .replace(/\s*-\}$/, '')  // Remove closing -}
          .replace(/^\s*\*\s*/, '') // Remove leading asterisks
          .trim();
        
        // Add to combined text with proper spacing
        if (allCommentText && cleanText) {
          allCommentText += '\n' + cleanText;
        } else if (cleanText) {
          allCommentText = cleanText;
        }
      });
      
      if (allCommentText) {
        // Split into lines and clean each line
        const lines = allCommentText.split('\n').map(line => {
          // Remove common comment prefixes and clean up, but preserve list markers
          return line
            .replace(/^\s*\*?\s*/, '') // Remove leading asterisks and whitespace
            .trim();
        }).filter(line => line.length > 0);
        
        if (lines.length > 0) {
          const commentBlock = document.createElement('div');
          commentBlock.className = 'preview-comment-block';
          
          // Process lines to detect lists and format them properly
          let currentList = null;
          let currentListType = null;
          let currentListItem = null;
          
          lines.forEach(line => {
            // Check if this line is a list item (be more specific about list detection)
            const bulletMatch = line.match(/^[-*+]\s+(.+)$/);
            const numberedMatch = line.match(/^\d+\.\s+(.+)$/);
            
            if (bulletMatch) {
              // This is a bullet list item
              if (currentListType !== 'ul') {
                // Close any existing list and start a new unordered list
                if (currentList) {
                  commentBlock.appendChild(currentList);
                }
                currentList = document.createElement('ul');
                currentList.className = 'preview-comment-list';
                currentListType = 'ul';
              }
              
              currentListItem = document.createElement('li');
              currentListItem.className = 'preview-comment-list-item';
              currentListItem.textContent = bulletMatch[1];
              currentList.appendChild(currentListItem);
              
            } else if (numberedMatch) {
              // This is a numbered list item
              if (currentListType !== 'ol') {
                // Close any existing list and start a new ordered list
                if (currentList) {
                  commentBlock.appendChild(currentList);
                }
                currentList = document.createElement('ol');
                currentList.className = 'preview-comment-list';
                currentListType = 'ol';
              }
              
              currentListItem = document.createElement('li');
              currentListItem.className = 'preview-comment-list-item';
              currentListItem.textContent = numberedMatch[1]; // Use the first capture group for the text
              currentList.appendChild(currentListItem);
              
            } else if (currentListItem && line.trim() !== '') {
              // This is a continuation line for the current list item
              // Add it to the current list item with a space
              currentListItem.textContent += ' ' + line;
              
            } else {
              // This is a regular line or empty line - close any existing list first
              if (currentList) {
                commentBlock.appendChild(currentList);
                currentList = null;
                currentListType = null;
                currentListItem = null;
              }
              
              // Only add non-empty lines as regular comment lines
              if (line.trim() !== '') {
                const commentLine = document.createElement('div');
                commentLine.className = 'preview-comment-line';
                commentLine.textContent = line;
                commentBlock.appendChild(commentLine);
              }
            }
          });
          
          // Don't forget to append any remaining list
          if (currentList) {
            commentBlock.appendChild(currentList);
          }
          
          commentContainer.appendChild(commentBlock);
        }
      }
      
      container.appendChild(commentContainer);
    }
    
    // Create line numbers container
    const lineNumbers = document.createElement('div');
    lineNumbers.className = 'preview-line-numbers';
    
    // Create code content container
    const codeContent = document.createElement('div');
    codeContent.className = 'preview-code-content';
    
    // Add each line with its number
    contextLines.forEach((line, index) => {
      // The actual line number in the document (startLineIndex is 0-based, but lines are 1-based)
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
      
      // Clone the line content more carefully to preserve whitespace and syntax highlighting
      const lineContentWrapper = document.createElement('div');
      lineContentWrapper.style.whiteSpace = 'pre';
      lineContentWrapper.innerHTML = line.innerHTML;
      
      codeLine.appendChild(lineContentWrapper);
      codeContent.appendChild(codeLine);
    });
    
    // Create preview code structure - use the same exact class structure as in the main content
    const previewCode = document.createElement('div');
    // Use the same class structure as the main Agda code blocks to inherit styles
    previewCode.className = 'Agda'; 
    
    // Create a code container to match the main content structure
    const codeContainer = document.createElement('div');
    codeContainer.className = 'code-container';
    codeContainer.appendChild(lineNumbers);
    codeContainer.appendChild(codeContent);
    
    previewCode.appendChild(codeContainer);
    container.appendChild(previewCode);
    
    return container;
  }
  
  /**
   * Fetch code from another file
   */
  async function fetchCodeFromFile(file, lineNumber, moduleName = '', blockId = 'B1') {
    try {
      const response = await fetch(file);
      if (!response.ok) {
        throw new Error(`Failed to fetch ${file}: ${response.status}`);
      }
      
      const html = await response.text();
      
      // Create a temporary document to parse the HTML
      const parser = new DOMParser();
      const doc = parser.parseFromString(html, 'text/html');
      
      // Find the target line using the block-specific ID
      const lineContentId = `${blockId}-LC${lineNumber}`;
      const targetLine = doc.getElementById(lineContentId);
      
      // If the specific block isn't found, try to find any line with that number
      // (fallback for files that might not have the updated format)
      if (!targetLine) {
        // Look for a line with the legacy format or in any block
        const legacyTarget = doc.getElementById(`LC${lineNumber}`);
        if (legacyTarget) {
          // Use the legacy target's code block
          const codeContainer = legacyTarget.closest('.code-content');
          if (codeContainer) {
            const allLines = Array.from(codeContainer.querySelectorAll('.code-line'));
            const targetIndex = allLines.indexOf(legacyTarget);
            
            if (targetIndex !== -1) {
              const { startIndex, endIndex, commentLines } = determineContextLines(allLines, targetIndex);
              const contextLines = allLines.slice(startIndex, endIndex + 1);
              return buildCodePreview(contextLines, lineNumber, startIndex, moduleName, 'B1', commentLines);
            }
          }
        }
        return null;
      }
      
      // Get the containing code block
      const codeContainer = targetLine.closest('.code-content');
      if (!codeContainer) return null;
      
      // Get all lines from the code container
      const allLines = Array.from(codeContainer.querySelectorAll('.code-line'));
      const targetIndex = allLines.indexOf(targetLine);
      
      if (targetIndex === -1) return null;
      
      // Determine context-aware start and end indexes
      const { startIndex, endIndex, commentLines } = determineContextLines(allLines, targetIndex);
      
      // Create a new container with the context lines
      const contextLines = allLines.slice(startIndex, endIndex + 1);
      
      // Build HTML for the code preview
      return buildCodePreview(contextLines, lineNumber, startIndex, moduleName, blockId, commentLines);
    } catch (error) {
      console.error('Error fetching preview:', error);
      return null;
    }
  }
  
  /**
   * Position the preview container near the link
   */
  function positionPreview(link) {
    if (!link || !previewContainer) return;
    
    const linkRect = link.getBoundingClientRect();
    const viewportWidth = window.innerWidth;
    const viewportHeight = window.innerHeight;
    
    // Reset any previous positioning
    previewContainer.style.maxHeight = '';
    previewContainer.style.maxWidth = '';
    
    // Allow the container to take its natural size first
    previewContainer.style.visibility = 'hidden';
    previewContainer.style.display = 'block';
    
    // Get container dimensions
    const containerWidth = previewContainer.offsetWidth;
    const containerHeight = previewContainer.offsetHeight;
    
    // Default position is below the link
    let top = linkRect.bottom + window.scrollY + 5;
    let left = linkRect.left + window.scrollX;
    
    // Check if the preview would go off the bottom of the viewport
    if (linkRect.bottom + containerHeight > viewportHeight) {
      // Position above the link instead
      top = linkRect.top + window.scrollY - containerHeight - 5;
      
      // If it would go off the top too, position it at the top of the viewport
      if (top < window.scrollY) {
        top = window.scrollY + 5;
        
        // Constrain height to fit in viewport
        const maxHeight = viewportHeight - 10;
        previewContainer.style.maxHeight = `${maxHeight}px`;
      }
    }
    
    // Check if the preview would go off the right of the viewport
    if (left + containerWidth > viewportWidth) {
      // Align right edge with viewport edge
      left = viewportWidth - containerWidth + window.scrollX - 5;
      
      // Don't let it go off the left either
      if (left < window.scrollX) {
        left = window.scrollX + 5;
        previewContainer.style.maxWidth = `${viewportWidth - 10}px`;
      }
    }
    
    // Apply the calculated position
    previewContainer.style.top = `${top}px`;
    previewContainer.style.left = `${left}px`;
    
    // Show the preview
    previewContainer.style.visibility = 'visible';
  }
  
  /**
   * Hide the preview
   */
  function hidePreview() {
    if (previewContainer) {
      previewContainer.style.display = 'none';
    }
    
    if (activeTimeout) {
      clearTimeout(activeTimeout);
      activeTimeout = null;
    }
    
    activeLink = null;
  }
})();