// Function to handle code block functionality with line numbers
(function() {
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
  
  // Handle highlighting of lines when line numbers are clicked
  function setupLineHighlighting() {
    const lineNumbers = document.querySelectorAll('.line-number');
    
    lineNumbers.forEach(lineNum => {
      lineNum.addEventListener('click', function(e) {
        e.preventDefault(); // Prevent default hash navigation
        
        // Remove highlight from all lines and line numbers first
        document.querySelectorAll('.code-line.highlighted').forEach(line => {
          line.classList.remove('highlighted');
        });
        document.querySelectorAll('.line-number.highlighted').forEach(num => {
          num.classList.remove('highlighted');
        });
        
        // Get the line number and block ID
        const num = this.getAttribute('data-line-number');
        const blockId = this.getAttribute('data-block-id') || 'block-1';
        if (!num) return;
        
        // Add highlight class to clicked line number
        this.classList.add('highlighted');
        
        // Find the corresponding code line and highlight it
        const lineContentId = `${blockId}-LC${num}`;
        const codeLine = document.getElementById(lineContentId);
        if (codeLine) {
          codeLine.classList.add('highlighted');
          
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
      });
    });
  }
  
  // Handle highlighting of lines when URL has fragment
  function highlightTargetLine() {
    // Clear any existing highlights first
    document.querySelectorAll('.code-line.highlighted').forEach(line => {
      line.classList.remove('highlighted');
    });
    document.querySelectorAll('.line-number.highlighted').forEach(num => {
      num.classList.remove('highlighted');
    });
    
    const hash = window.location.hash;
    if (hash) {
      // Check for block-specific line format: #block-X-LY
      const blockLineMatch = hash.match(/#(B\d+)-L(\d+)$/);
      if (blockLineMatch) {
        const blockId = blockLineMatch[1];
        const lineNum = blockLineMatch[2];
        const lineId = `${blockId}-L${lineNum}`;
        const lineContentId = `${blockId}-LC${lineNum}`;
        
        const codeLine = document.getElementById(lineContentId);
        const lineNumEl = document.getElementById(lineId);
        
        if (codeLine) {
          // Highlight the target line
          codeLine.classList.add('highlighted');
          
          // Highlight the corresponding line number
          if (lineNumEl) {
            lineNumEl.classList.add('highlighted');
          }
          
          // Scroll the line into view
          setTimeout(() => {
            codeLine.scrollIntoView({
              behavior: 'smooth', 
              block: 'center'
            });
          }, 100); // Small delay to ensure DOM is ready
        }
      } else if (hash.startsWith('#L')) {
        // Legacy format support: #L123 (for backward compatibility)
        // Try to find it in the first block
        const lineNum = hash.substring(2);
        const blockId = 'B1';
        const lineContentId = `${blockId}-LC${lineNum}`;
        const lineId = `${blockId}-L${lineNum}`;
        
        const codeLine = document.getElementById(lineContentId);
        const lineNumEl = document.getElementById(lineId);
        
        if (codeLine) {
          // Highlight the target line
          codeLine.classList.add('highlighted');
          
          // Highlight the corresponding line number
          if (lineNumEl) {
            lineNumEl.classList.add('highlighted');
          }
          
          // Scroll the line into view
          setTimeout(() => {
            codeLine.scrollIntoView({
              behavior: 'smooth', 
              block: 'center'
            });
          }, 100); // Small delay to ensure DOM is ready
        }
      }
    }
  }
  
  // Run on page load and when hash changes
  setupLineHighlighting();
  highlightTargetLine();
  window.addEventListener('hashchange', highlightTargetLine);
})(); 