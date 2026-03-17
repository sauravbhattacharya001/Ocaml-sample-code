/**
 * Tests for Tail Recursion Converter (docs/tail_recursion_converter.html)
 * @jest-environment jsdom
 */

const fs = require('fs');
const path = require('path');

let html;

beforeAll(() => {
  html = fs.readFileSync(path.join(__dirname, '..', 'docs', 'tail_recursion_converter.html'), 'utf8');
});

function loadPage() {
  document.documentElement.innerHTML = '';
  document.write(html);
  document.close();
}

describe('Tail Recursion Converter', () => {
  beforeEach(() => {
    loadPage();
  });

  // Structure tests
  test('page loads with title', () => {
    expect(document.title).toBe('OCaml Tail Recursion Converter');
  });

  test('has all example tabs', () => {
    const tabs = document.querySelectorAll('.tab');
    expect(tabs.length).toBe(10);
    const labels = Array.from(tabs).map(t => t.dataset.tab);
    expect(labels).toContain('factorial');
    expect(labels).toContain('fibonacci');
    expect(labels).toContain('list-map');
    expect(labels).toContain('converter');
    expect(labels).toContain('quiz');
  });

  test('factorial panel is active by default', () => {
    const panel = document.getElementById('panel-factorial');
    expect(panel.classList.contains('active')).toBe(true);
  });

  test('other panels are hidden by default', () => {
    const panel = document.getElementById('panel-fibonacci');
    expect(panel.classList.contains('active')).toBe(false);
  });

  // Tab switching
  test('clicking a tab switches panels', () => {
    const fibTab = document.querySelector('[data-tab="fibonacci"]');
    fibTab.click();
    expect(fibTab.classList.contains('active')).toBe(true);
    expect(document.getElementById('panel-fibonacci').classList.contains('active')).toBe(true);
    expect(document.getElementById('panel-factorial').classList.contains('active')).toBe(false);
  });

  test('clicking quiz tab shows quiz panel', () => {
    document.querySelector('[data-tab="quiz"]').click();
    expect(document.getElementById('panel-quiz').classList.contains('active')).toBe(true);
  });

  test('clicking converter tab shows converter', () => {
    document.querySelector('[data-tab="converter"]').click();
    expect(document.getElementById('panel-converter').classList.contains('active')).toBe(true);
  });

  // Content tests
  test('each example has naive and tail-recursive code', () => {
    const panels = ['factorial', 'fibonacci', 'list-length', 'list-reverse', 'list-map', 'sum-list', 'flatten'];
    panels.forEach(p => {
      const panel = document.getElementById('panel-' + p);
      const codeBlocks = panel.querySelectorAll('.code-block');
      expect(codeBlocks.length).toBeGreaterThanOrEqual(2);
    });
  });

  test('each example has transformation steps', () => {
    const panels = ['factorial', 'fibonacci', 'list-length', 'list-reverse', 'list-map', 'sum-list', 'flatten', 'gcd'];
    panels.forEach(p => {
      const panel = document.getElementById('panel-' + p);
      const steps = panel.querySelectorAll('.step');
      expect(steps.length).toBeGreaterThan(0);
    });
  });

  test('complexity cards show stack usage', () => {
    const cards = document.querySelectorAll('#panel-factorial .complexity-card');
    expect(cards.length).toBe(4);
    const text = Array.from(cards).map(c => c.textContent);
    expect(text.some(t => t.includes('O(n)'))).toBe(true);
    expect(text.some(t => t.includes('O(1)'))).toBe(true);
  });

  test('GCD panel notes it is already tail-recursive', () => {
    const gcd = document.getElementById('panel-gcd');
    expect(gcd.textContent).toContain('Already Tail Recursive');
  });

  // Converter tests
  test('converter textarea exists', () => {
    const textarea = document.getElementById('input-code');
    expect(textarea).toBeTruthy();
    expect(textarea.tagName).toBe('TEXTAREA');
  });

  test('converter shows warning for empty input', () => {
    document.querySelector('[data-tab="converter"]').click();
    document.getElementById('input-code').value = '';
    document.querySelector('.btn').click();
    const out = document.getElementById('converter-output');
    expect(out.textContent).toContain('Please enter some code');
  });

  test('converter detects non-rec function', () => {
    document.getElementById('input-code').value = 'let double x = x * 2';
    document.querySelector('.btn').click();
    const out = document.getElementById('converter-output');
    expect(out.textContent).toContain('Could not find');
  });

  test('converter analyzes factorial', () => {
    document.getElementById('input-code').value = 'let rec factorial n = if n <= 1 then 1 else n * factorial (n - 1)';
    document.querySelector('.btn').click();
    const out = document.getElementById('converter-output');
    expect(out.textContent).toContain('factorial');
    expect(out.textContent).toContain('accumulator');
  });

  test('converter recognizes tail-recursive function', () => {
    document.getElementById('input-code').value = 'let rec gcd a b = if b = 0 then a else gcd b (a mod b)';
    document.querySelector('.btn').click();
    const out = document.getElementById('converter-output');
    expect(out.textContent).toContain('already be tail-recursive');
  });

  // Quiz tests
  test('quiz renders all questions', () => {
    document.querySelector('[data-tab="quiz"]').click();
    const questions = document.querySelectorAll('.quiz-q');
    expect(questions.length).toBe(6);
  });

  test('quiz question has options', () => {
    const opts = document.querySelectorAll('[data-q="0"]');
    expect(opts.length).toBeGreaterThan(1);
  });

  test('answering quiz correctly shows green', () => {
    // Q1 answer is index 1 (B)
    const opt = document.querySelector('[data-q="0"][data-o="1"]');
    opt.click();
    expect(opt.classList.contains('correct')).toBe(true);
    expect(document.getElementById('result-0').textContent).toContain('✅');
  });

  test('answering quiz incorrectly shows red', () => {
    const opt = document.querySelector('[data-q="0"][data-o="0"]');
    opt.click();
    expect(opt.classList.contains('wrong')).toBe(true);
    expect(document.getElementById('result-0').textContent).toContain('❌');
  });

  test('score bar appears after answering', () => {
    document.querySelector('[data-q="0"][data-o="1"]').click();
    const bar = document.getElementById('score-bar');
    expect(bar.style.display).toBe('flex');
  });

  test('quiz options are disabled after answering', () => {
    document.querySelector('[data-q="0"][data-o="1"]').click();
    const opts = document.querySelectorAll('[data-q="0"]');
    opts.forEach(o => expect(o.classList.contains('disabled')).toBe(true));
  });

  test('correct answer is always highlighted', () => {
    // Answer wrong on Q1
    document.querySelector('[data-q="0"][data-o="0"]').click();
    const correct = document.querySelector('[data-q="0"][data-o="1"]');
    expect(correct.classList.contains('correct')).toBe(true);
  });

  // Copy buttons
  test('copy buttons exist on code blocks', () => {
    const buttons = document.querySelectorAll('.copy-btn');
    expect(buttons.length).toBeGreaterThan(5);
  });

  // Responsive
  test('has viewport meta tag', () => {
    const meta = document.querySelector('meta[name="viewport"]');
    expect(meta).toBeTruthy();
  });

  // Dark theme
  test('uses dark background', () => {
    const body = document.body;
    const style = getComputedStyle(body);
    // Check CSS variable is set
    const root = document.documentElement;
    expect(html).toContain('--bg: #1a1b26');
  });

  test('header contains description', () => {
    const header = document.querySelector('.header');
    expect(header.textContent).toContain('tail-recursive');
  });

  test('all 8 example panels exist', () => {
    const ids = ['factorial', 'fibonacci', 'list-length', 'list-reverse', 'list-map', 'sum-list', 'flatten', 'gcd'];
    ids.forEach(id => {
      expect(document.getElementById('panel-' + id)).toBeTruthy();
    });
  });
});
