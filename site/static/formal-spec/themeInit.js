(function() {
  // Check for theme preference in localStorage
  const savedTheme = localStorage.getItem('theme');
  if (savedTheme === 'dark') {
    document.documentElement.classList.add('dark-theme');
  }
})(); 