// Function to handle code block functionality with line numbers
(function() {
  // Track the last clicked line for range selection
  let lastClickedLine = null;
  let lastClickedBlockId = null;

  // Function to copy code without line numbers
  function copyCode(event) {
    const button = event.currentTarget;
    const pre = button.closest('pre.Agda');
    if (!pre) return;
    
    const codeContent = pre.querySelector('.code-content');
    if (!codeContent) return;
    
    // Extract text content from code lines, preserving structure
    const codeLines = Array.from(codeContent.querySelectorAll('.code-line'));
    const codeText = codeLines.map(line => line.textContent).join('\n');
    
    // Create temporary textarea to copy from
    const textarea = document.createElement('textarea');
    textarea.value = codeText;
    textarea.style.position = 'absolute';
    textarea.style.left = '-9999px';
    document.body.appendChild(textarea);
    textarea.select();
    
    try {
      document.execCommand('copy');
      // Show success state
      button.classList.add('copy-success');
      setTimeout(() => {
        button.classList.remove('copy-success');
      }, 2000);
    } catch (err) {
      console.error('Failed to copy code: ', err);
    }
    
    document.body.removeChild(textarea);
  }
  
  // Add click event listeners to all copy buttons
  const copyButtons = document.querySelectorAll('.copy-code-button');
  copyButtons.forEach(button => {
    button.addEventListener('click', copyCode);
  });
  
  // Function to highlight a range of lines
  function highlightLineRange(blockId, startLine, endLine) {
    // Ensure startLine <= endLine
    if (startLine > endLine) {
      [startLine, endLine] = [endLine, startLine];
    }
    
    // Clear all existing highlights first
    clearAllHighlights();
    
    // Highlight the range of lines
    for (let lineNum = startLine; lineNum <= endLine; lineNum++) {
      const lineNumberId = `${blockId}-L${lineNum}`;
      const lineContentId = `${blockId}-LC${lineNum}`;
      
      const lineNumEl = document.getElementById(lineNumberId);
      const lineContentEl = document.getElementById(lineContentId);
      
      if (lineNumEl) {
        lineNumEl.classList.add('highlighted');
        
        // Add range-specific classes for styling
        if (startLine === endLine) {
          // Single line
          lineNumEl.classList.add('range-single');
        } else if (lineNum === startLine) {
          // First line in range
          lineNumEl.classList.add('range-start');
        } else if (lineNum === endLine) {
          // Last line in range
          lineNumEl.classList.add('range-end');
        } else {
          // Middle line in range
          lineNumEl.classList.add('range-middle');
        }
      }
      
      if (lineContentEl) {
        lineContentEl.classList.add('highlighted');
        
        // Add range-specific classes for styling
        if (startLine === endLine) {
          // Single line
          lineContentEl.classList.add('range-single');
        } else if (lineNum === startLine) {
          // First line in range
          lineContentEl.classList.add('range-start');
        } else if (lineNum === endLine) {
          // Last line in range
          lineContentEl.classList.add('range-end');
        } else {
          // Middle line in range
          lineContentEl.classList.add('range-middle');
        }
      }
    }
  }
  
  // Function to clear all highlights
  function clearAllHighlights() {
    document.querySelectorAll('.code-line.highlighted').forEach(line => {
      line.classList.remove('highlighted', 'range-start', 'range-middle', 'range-end', 'range-single');
    });
    document.querySelectorAll('.line-number.highlighted').forEach(num => {
      num.classList.remove('highlighted', 'range-start', 'range-middle', 'range-end', 'range-single');
    });
  }
  
  // Handle highlighting of lines when line numbers are clicked
  function setupLineHighlighting() {
    const lineNumbers = document.querySelectorAll('.line-number');
    
    lineNumbers.forEach(lineNum => {
      lineNum.addEventListener('click', function(e) {
        e.preventDefault(); // Prevent default hash navigation
        
        // Get the line number and block ID
        const num = parseInt(this.getAttribute('data-line-number'));
        const blockId = this.getAttribute('data-block-id') || 'block-1';
        if (!num) return;
        
        // Check if shift is held for range selection
        if (e.shiftKey && lastClickedLine && lastClickedBlockId === blockId) {
          // Range selection: highlight from last clicked line to current line
          const startLine = Math.min(lastClickedLine, num);
          const endLine = Math.max(lastClickedLine, num);
          
          highlightLineRange(blockId, startLine, endLine);
          
          // Update URL hash for range
          const newUrl = window.location.pathname + window.location.search + `#${blockId}-L${startLine}-${endLine}`;
          history.pushState(null, '', newUrl);
          
          // Scroll the range into view (scroll to the start of the range)
          const startLineContentId = `${blockId}-LC${startLine}`;
          const startLineEl = document.getElementById(startLineContentId);
          if (startLineEl) {
            startLineEl.scrollIntoView({
              behavior: 'smooth',
              block: 'center'
            });
          }
        } else {
          // Single line selection
          clearAllHighlights();
          
          // Add highlight class to clicked line number
          this.classList.add('highlighted', 'range-single');
          
          // Find the corresponding code line and highlight it
          const lineContentId = `${blockId}-LC${num}`;
          const codeLine = document.getElementById(lineContentId);
          if (codeLine) {
            codeLine.classList.add('highlighted', 'range-single');
            
            // Update URL hash without causing a jump
            const lineId = `${blockId}-L${num}`;
            const newUrl = window.location.pathname + window.location.search + '#' + lineId;
            history.pushState(null, '', newUrl);
            
            // Scroll the element into view
            codeLine.scrollIntoView({
              behavior: 'smooth',
              block: 'center'
            });
          }
          
          // Update last clicked line for future range selections
          lastClickedLine = num;
          lastClickedBlockId = blockId;
        }
      });
    });
  }
  
  // Handle highlighting of lines when URL has fragment
  function highlightTargetLine() {
    // Clear any existing highlights first
    clearAllHighlights();
    
    const hash = window.location.hash;
    if (hash) {
      // Check for range format: #block-X-LY-Z (lines Y through Z)
      const rangeMatch = hash.match(/#(B\d+)-L(\d+)-(\d+)$/);
      if (rangeMatch) {
        const blockId = rangeMatch[1];
        const startLine = parseInt(rangeMatch[2]);
        const endLine = parseInt(rangeMatch[3]);
        
        highlightLineRange(blockId, startLine, endLine);
        
        // Scroll to the start of the range
        const startLineContentId = `${blockId}-LC${startLine}`;
        const startLineEl = document.getElementById(startLineContentId);
        if (startLineEl) {
          setTimeout(() => {
            startLineEl.scrollIntoView({
              behavior: 'smooth', 
              block: 'center'
            });
          }, 100);
        }
        
        // Update tracking variables
        lastClickedLine = endLine; // Set to the end of the range for future selections
        lastClickedBlockId = blockId;
        return;
      }
      
      // Check for block-specific line format: #block-X-LY
      const blockLineMatch = hash.match(/#(B\d+)-L(\d+)$/);
      if (blockLineMatch) {
        const blockId = blockLineMatch[1];
        const lineNum = parseInt(blockLineMatch[2]);
        const lineId = `${blockId}-L${lineNum}`;
        const lineContentId = `${blockId}-LC${lineNum}`;
        
        const codeLine = document.getElementById(lineContentId);
        const lineNumEl = document.getElementById(lineId);
        
        if (codeLine) {
          // Highlight the target line
          codeLine.classList.add('highlighted', 'range-single');
          
          // Highlight the corresponding line number
          if (lineNumEl) {
            lineNumEl.classList.add('highlighted', 'range-single');
          }
          
          // Scroll the line into view
          setTimeout(() => {
            codeLine.scrollIntoView({
              behavior: 'smooth', 
              block: 'center'
            });
          }, 100); // Small delay to ensure DOM is ready
          
          // Update tracking variables
          lastClickedLine = lineNum;
          lastClickedBlockId = blockId;
        }
      } else if (hash.startsWith('#L')) {
        // Legacy format support: #L123 (for backward compatibility)
        // Try to find it in the first block
        const lineNum = parseInt(hash.substring(2));
        const blockId = 'B1';
        const lineContentId = `${blockId}-LC${lineNum}`;
        const lineId = `${blockId}-L${lineNum}`;
        
        const codeLine = document.getElementById(lineContentId);
        const lineNumEl = document.getElementById(lineId);
        
        if (codeLine) {
          // Highlight the target line
          codeLine.classList.add('highlighted', 'range-single');
          
          // Highlight the corresponding line number
          if (lineNumEl) {
            lineNumEl.classList.add('highlighted', 'range-single');
          }
          
          // Scroll the line into view
          setTimeout(() => {
            codeLine.scrollIntoView({
              behavior: 'smooth', 
              block: 'center'
            });
          }, 100); // Small delay to ensure DOM is ready
          
          // Update tracking variables
          lastClickedLine = lineNum;
          lastClickedBlockId = blockId;
        }
      }
    }
  }
  
  // Run on page load and when hash changes
  setupLineHighlighting();
  highlightTargetLine();
  window.addEventListener('hashchange', highlightTargetLine);
})(); 