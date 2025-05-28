(function() {
  // Check if theme preference exists in localStorage
  const savedTheme = localStorage.getItem('theme');
  if (savedTheme === 'dark') {
    document.documentElement.classList.add('dark-theme');
  }

  // Add toggle functionality
  document.querySelector('.theme-toggle').addEventListener('click', function() {
    const html = document.documentElement;
    const isDark = html.classList.contains('dark-theme');
    
    if (isDark) {
      html.classList.remove('dark-theme');
      localStorage.setItem('theme', 'light');
    } else {
      html.classList.add('dark-theme');
      localStorage.setItem('theme', 'dark');
    }
  });
})(); 