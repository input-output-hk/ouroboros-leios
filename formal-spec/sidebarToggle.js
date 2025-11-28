// Mobile sidebar toggle functionality
(function() {
  document.addEventListener('DOMContentLoaded', function() {
    const body = document.body;
    const menuToggle = document.querySelector('.menu-toggle');
    const sidebar = document.querySelector('.sidebar');
    
    // Create sidebar overlay element
    const sidebarOverlay = document.createElement('div');
    sidebarOverlay.className = 'sidebar-overlay';
    document.body.appendChild(sidebarOverlay);
    
    // Toggle sidebar function
    function toggleSidebar() {
      body.classList.toggle('sidebar-open');
    }
    
    // Close sidebar function
    function closeSidebar() {
      body.classList.remove('sidebar-open');
    }
    
    // Add click handler to menu toggle button
    if (menuToggle) {
      menuToggle.addEventListener('click', function(e) {
        e.preventDefault();
        e.stopPropagation();
        toggleSidebar();
      });
    }
    
    // Close sidebar when clicking on overlay
    sidebarOverlay.addEventListener('click', function(e) {
      e.preventDefault();
      closeSidebar();
    });
    
    // Close sidebar when clicking on a module link (for mobile navigation)
    if (sidebar) {
      const moduleLinks = sidebar.querySelectorAll('.module-link');
      moduleLinks.forEach(link => {
        link.addEventListener('click', function() {
          // Only close on mobile (when menu toggle is visible)
          if (window.getComputedStyle(menuToggle).display !== 'none') {
            closeSidebar();
          }
        });
      });
    }
    
    // Handle escape key to close sidebar
    document.addEventListener('keydown', function(e) {
      if (e.key === 'Escape' && body.classList.contains('sidebar-open')) {
        closeSidebar();
      }
    });
    
    // Close sidebar when window is resized to desktop size
    window.addEventListener('resize', function() {
      // If we're now on desktop size and sidebar is open, close it
      if (window.innerWidth > 768 && body.classList.contains('sidebar-open')) {
        closeSidebar();
      }
    });
    
    // Prevent body scroll when sidebar is open on mobile
    const observer = new MutationObserver(function(mutations) {
      mutations.forEach(function(mutation) {
        if (mutation.type === 'attributes' && mutation.attributeName === 'class') {
          if (body.classList.contains('sidebar-open')) {
            // Prevent scrolling on mobile when sidebar is open
            if (window.innerWidth <= 768) {
              body.style.overflow = 'hidden';
            }
          } else {
            // Restore scrolling
            body.style.overflow = '';
          }
        }
      });
    });
    
    observer.observe(body, {
      attributes: true,
      attributeFilter: ['class']
    });
  });
})(); 