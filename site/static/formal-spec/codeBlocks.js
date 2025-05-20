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
        
        // Get the line number
        const num = this.getAttribute('data-line-number');
        if (!num) return;
        
        // Add highlight class to clicked line number
        this.classList.add('highlighted');
        
        // Find the corresponding code line and highlight it
        const lineId = 'LC' + num;
        const codeLine = document.getElementById(lineId);
        if (codeLine) {
          codeLine.classList.add('highlighted');
          
          // Update URL hash without causing a jump
          const newUrl = window.location.pathname + window.location.search + '#L' + num;
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
    if (hash && hash.startsWith('#L')) {
      // Extract the line number from the hash
      const lineNum = hash.substring(2);
      const lineId = 'LC' + lineNum;
      const codeLine = document.getElementById(lineId);
      const lineNumEl = document.getElementById('L' + lineNum);
      
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
  
  // Run on page load and when hash changes
  setupLineHighlighting();
  highlightTargetLine();
  window.addEventListener('hashchange', highlightTargetLine);
})(); 