// RH Formalization Project — Minimal vanilla JS
// Progressive enhancement for navigation

document.addEventListener('DOMContentLoaded', function() {
  // Set active nav link based on current page
  const currentPage = window.location.pathname.split('/').pop() || 'index.html';
  document.querySelectorAll('nav a').forEach(link => {
    const href = link.getAttribute('href');
    if (href === currentPage || (currentPage === '' && href === 'index.html')) {
      link.classList.add('active');
    } else {
      link.classList.remove('active');
    }
  });

  // Smooth scroll for anchor links
  document.querySelectorAll('a[href^="#"]').forEach(anchor => {
    anchor.addEventListener('click', function (e) {
      const href = this.getAttribute('href');
      if (href !== '#') {
        e.preventDefault();
        const target = document.querySelector(href);
        if (target) {
          target.scrollIntoView({ behavior: 'smooth' });
        }
      }
    });
  });

  // Copy code block functionality (if needed)
  document.querySelectorAll('pre').forEach(pre => {
    const code = pre.textContent;
    const button = document.createElement('button');
    button.className = 'button copy-btn';
    button.textContent = 'Copy';
    button.style.marginBottom = '0.5rem';
    button.addEventListener('click', function() {
      navigator.clipboard.writeText(code);
      button.textContent = 'Copied!';
      setTimeout(() => { button.textContent = 'Copy'; }, 2000);
    });
    pre.parentElement.insertBefore(button, pre);
  });
});
