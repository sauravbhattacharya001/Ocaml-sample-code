/**
 * @jest-environment node
 *
 * Tests for docs/error-guide.html — OCaml Error Guide
 */
'use strict';

const fs = require('fs');
const path = require('path');
const { JSDOM } = require('jsdom');

const html = fs.readFileSync(path.join(__dirname, '..', 'docs', 'error-guide.html'), 'utf8');

function createDom() {
  const dom = new JSDOM(html, { runScripts: 'dangerously', pretendToBeVisual: true });
  return dom.window.document;
}

describe('OCaml Error Guide', () => {
  let doc;
  beforeEach(() => { doc = createDom(); });

  describe('page structure', () => {
    test('has title', () => {
      expect(doc.title).toContain('OCaml Error Guide');
    });
    test('has header with title', () => {
      const h1 = doc.querySelector('.header h1');
      expect(h1).not.toBeNull();
      expect(h1.textContent).toContain('Error Guide');
    });
    test('has search box', () => {
      expect(doc.getElementById('search')).not.toBeNull();
    });
    test('has filter buttons', () => {
      expect(doc.querySelectorAll('.filter-btn').length).toBeGreaterThanOrEqual(4);
    });
    test('has stats bar', () => {
      expect(doc.querySelector('.stats-bar')).not.toBeNull();
    });
    test('has container', () => {
      expect(doc.getElementById('container')).not.toBeNull();
    });
  });

  describe('error cards', () => {
    test('renders 30 error cards', () => {
      expect(doc.querySelectorAll('.error-card').length).toBe(30);
    });
    test('each card has a title', () => {
      doc.querySelectorAll('.error-title').forEach(t => {
        expect(t.textContent.trim().length).toBeGreaterThan(0);
      });
    });
    test('each card has severity dot', () => {
      expect(doc.querySelectorAll('.severity-dot').length).toBe(doc.querySelectorAll('.error-card').length);
    });
    test('cards start collapsed', () => {
      doc.querySelectorAll('.error-card').forEach(c => {
        expect(c.classList.contains('open')).toBe(false);
      });
    });
    test('card body has code examples', () => {
      const card = doc.querySelector('.error-card');
      card.classList.add('open');
      expect(card.querySelector('.code-bad')).not.toBeNull();
      expect(card.querySelector('.code-good')).not.toBeNull();
    });
  });

  describe('severity', () => {
    test('has error and warning cards', () => {
      expect(doc.querySelectorAll('.severity-error').length).toBeGreaterThan(0);
      expect(doc.querySelectorAll('.severity-warning').length).toBeGreaterThan(0);
    });
  });

  describe('search', () => {
    test('filters cards by query', () => {
      const search = doc.getElementById('search');
      const total = doc.querySelectorAll('.error-card').length;
      search.value = 'unbound value';
      search.dispatchEvent(new doc.defaultView.Event('input'));
      const filtered = doc.querySelectorAll('.error-card').length;
      expect(filtered).toBeLessThan(total);
      expect(filtered).toBeGreaterThan(0);
    });
    test('shows no results message for nonsense', () => {
      const search = doc.getElementById('search');
      search.value = 'xyzzyqwertynonsense123';
      search.dispatchEvent(new doc.defaultView.Event('input'));
      expect(doc.querySelectorAll('.error-card').length).toBe(0);
      expect(doc.querySelector('.no-results')).not.toBeNull();
    });
    test('case-insensitive', () => {
      const search = doc.getElementById('search');
      search.value = 'UNBOUND';
      search.dispatchEvent(new doc.defaultView.Event('input'));
      expect(doc.querySelectorAll('.error-card').length).toBeGreaterThan(0);
    });
  });

  describe('filters', () => {
    test('error filter shows only errors', () => {
      doc.querySelector('[data-filter="error"]').click();
      doc.querySelectorAll('.error-card').forEach(c => {
        expect(c.classList.contains('severity-error')).toBe(true);
      });
    });
    test('warning filter shows only warnings', () => {
      doc.querySelector('[data-filter="warning"]').click();
      doc.querySelectorAll('.error-card').forEach(c => {
        expect(c.classList.contains('severity-warning')).toBe(true);
      });
    });
    test('beginner filter works', () => {
      doc.querySelector('[data-filter="beginner"]').click();
      const cards = doc.querySelectorAll('.error-card');
      expect(cards.length).toBeGreaterThan(0);
      cards.forEach(c => {
        expect(c.querySelector('.tag.beginner')).not.toBeNull();
      });
    });
    test('all restores everything', () => {
      doc.querySelector('[data-filter="beginner"]').click();
      const fewer = doc.querySelectorAll('.error-card').length;
      doc.querySelector('[data-filter="all"]').click();
      expect(doc.querySelectorAll('.error-card').length).toBeGreaterThan(fewer);
    });
  });

  describe('expand/collapse', () => {
    test('clicking header toggles card', () => {
      const header = doc.querySelector('.error-header');
      header.click();
      expect(header.parentElement.classList.contains('open')).toBe(true);
      header.click();
      expect(header.parentElement.classList.contains('open')).toBe(false);
    });
    test('expand all', () => {
      doc.getElementById('expand-all-btn').click();
      doc.querySelectorAll('.error-card').forEach(c => expect(c.classList.contains('open')).toBe(true));
    });
    test('collapse all after expand', () => {
      const btn = doc.getElementById('expand-all-btn');
      btn.click();
      btn.click();
      doc.querySelectorAll('.error-card').forEach(c => expect(c.classList.contains('open')).toBe(false));
    });
  });

  describe('content quality', () => {
    test('every card has explanation', () => {
      doc.querySelectorAll('.error-card').forEach(card => {
        card.classList.add('open');
        expect(card.querySelector('.explanation').textContent.trim().length).toBeGreaterThan(20);
      });
    });
    test('covers key OCaml errors', () => {
      const text = doc.getElementById('container').textContent.toLowerCase();
      expect(text).toContain('unbound value');
      expect(text).toContain('pattern');
      expect(text).toContain('syntax');
    });
    test('has tips', () => {
      expect(doc.querySelectorAll('.tip-box').length).toBeGreaterThan(15);
    });
  });

  describe('stats', () => {
    test('shown count matches cards', () => {
      const count = parseInt(doc.getElementById('shown-count').textContent);
      expect(count).toBe(doc.querySelectorAll('.error-card').length);
    });
    test('category count positive', () => {
      expect(parseInt(doc.getElementById('cat-count').textContent)).toBeGreaterThan(0);
    });
  });
});
