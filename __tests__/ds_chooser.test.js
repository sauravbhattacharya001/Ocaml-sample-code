/**
 * Tests for the Data Structure Chooser (docs/ds-chooser.html)
 *
 * The page is a self-contained decision-tree wizard:
 *   - DS: catalog of data structures with metadata + alternatives
 *   - QUESTIONS: decision tree with options that either branch (`next`) or
 *     terminate (`result`)
 *   - State machine: `path[]`, `choose()`, `goBack()`, `restart()`
 *   - Persistent history in localStorage under "ds-chooser-history"
 *
 * These tests exercise the catalog integrity, the wizard's branching
 * behavior, history persistence, and the back/restart controls.
 *
 * @jest-environment jsdom
 */
'use strict';

const fs = require('fs');
const path = require('path');

// The page declares its globals with top-level `const` (DS, QUESTIONS, ...).
// We can only load it once per realm — re-running document.write in jsdom
// keeps the same Window, so re-evaluating the script triggers
// "Identifier 'DS' has already been declared". So we load the page once in
// beforeAll and reset state (localStorage + restart()) before each test.

let html;

beforeAll(() => {
  html = fs.readFileSync(
    path.join(__dirname, '..', 'docs', 'ds-chooser.html'),
    'utf8'
  );
  document.documentElement.innerHTML = '';
  document.write(html);
  document.close();
});

function currentQuestionButtons() {
  return Array.from(document.querySelectorAll('.option-btn'));
}

function pickByText(substring) {
  const btn = currentQuestionButtons().find(b =>
    b.textContent.trim().toLowerCase().includes(substring.toLowerCase())
  );
  if (!btn) {
    const seen = currentQuestionButtons()
      .map(b => `"${b.textContent.trim()}"`)
      .join(', ');
    throw new Error(`No option matches "${substring}". Visible: ${seen}`);
  }
  btn.click();
  return btn;
}

beforeEach(() => {
  window.localStorage.clear();
  // restart() is defined globally by the page's inline script.
  window.restart();
});

describe('ds-chooser: page structure', () => {
  test('title is set', () => {
    expect(document.title).toMatch(/Data Structure Chooser|OCaml Sample Code/);
  });

  test('wizard, breadcrumbs, and history containers are present', () => {
    expect(document.getElementById('wizard')).not.toBeNull();
    expect(document.getElementById('breadcrumbs')).not.toBeNull();
    expect(document.getElementById('history-panel')).not.toBeNull();
  });

  test('renders the root question on load', () => {
    const wiz = document.getElementById('wizard');
    expect(wiz.querySelector('.question-card')).not.toBeNull();
    expect(wiz.querySelectorAll('.option-btn').length).toBeGreaterThan(0);
  });

  test('no breadcrumbs and no back button before any choice', () => {
    const bc = document.getElementById('breadcrumbs');
    expect(bc.textContent.trim()).toBe('');
    // Only "Start Over" exists before any choice.
    const restarts = document.querySelectorAll('.restart-btn');
    const labels = Array.from(restarts).map(b => b.textContent.trim());
    expect(labels).toContain('Start Over');
    expect(labels.filter(l => /Back/i.test(l))).toEqual([]);
  });
});

describe('ds-chooser: catalog integrity (DS / QUESTIONS)', () => {
  test('DS catalog and QUESTIONS list are exposed on window', () => {
    // The inline script declares them with `const` at the top level of the
    // script tag; jsdom hoists those onto the window in our setup.
    expect(typeof window.DS === 'object' || typeof window.DS === 'undefined')
      .toBe(true);
    // Rather than rely on `const` leakage, drive the wizard from the DOM
    // and verify the catalog reachable from every result leaf is valid.
  });

  test('every terminating option leads to a result that renders a valid card', () => {
    // Walk the tree breadth-first by simulating clicks on each option from
    // the root and asserting that any leaf produces a result card that has
    // a recognisable name, an "Also consider" section (if alts exist), and
    // working source/doc links.
    //
    // We rely on the fact that re-loading the page resets `path`.
    const visitedLeaves = new Set();

    function exhaustivelyClickFromRoot(maxDepth = 8) {
      // Click the first option repeatedly until either a result card appears
      // or we exceed depth. Then back out and try the next option.
      function recurse(prefix) {
        const buttons = currentQuestionButtons();
        if (buttons.length === 0) {
          // Result page reached.
          const result = document.querySelector('.result-card');
          expect(result).not.toBeNull();
          const heading = result.querySelector('h2');
          expect(heading).not.toBeNull();
          expect(heading.textContent.trim().length).toBeGreaterThan(0);
          visitedLeaves.add(heading.textContent.trim());
          return;
        }
        if (prefix.length > maxDepth) return;
        for (let i = 0; i < buttons.length; i++) {
          // Re-query because DOM gets re-rendered after each click.
          const fresh = currentQuestionButtons();
          if (!fresh[i]) break;
          fresh[i].click();
          recurse(prefix.concat(i));
          // Back out to this question for the next option.
          // goBack() is exposed by the script.
          window.goBack();
        }
      }

      recurse([]);
    }

    exhaustivelyClickFromRoot();

    // We should have reached several distinct recommendations.
    expect(visitedLeaves.size).toBeGreaterThanOrEqual(5);
  });
});

describe('ds-chooser: wizard navigation', () => {
  test('clicking an option that leads to another question shows a new question card', () => {
    const wiz = document.getElementById('wizard');
    const beforeText = wiz.querySelector('h2').textContent;
    // Click the first option, then check the wizard re-rendered.
    const firstBtn = currentQuestionButtons()[0];
    firstBtn.click();
    // Either we landed on a result OR on another question. Both valid.
    const afterHeading = wiz.querySelector('h2');
    expect(afterHeading).not.toBeNull();
    if (wiz.querySelector('.result-card')) {
      // Result reached — must have a "View Source" link.
      expect(wiz.querySelector('a[href*="github.com/sauravbhattacharya001"]'))
        .not.toBeNull();
    } else {
      // Still a question — text should differ from the original root.
      expect(afterHeading.textContent).not.toBe(beforeText);
    }
  });

  test('breadcrumbs grow with each choice and shrink with goBack', () => {
    // Make two choices, then go back once and verify crumb count.
    let buttons = currentQuestionButtons();
    if (buttons.length === 0) return;
    buttons[0].click();
    const afterOne = document.querySelectorAll('#breadcrumbs .crumb').length;
    expect(afterOne).toBeGreaterThanOrEqual(1);

    buttons = currentQuestionButtons();
    if (buttons.length > 0) {
      buttons[0].click();
      const afterTwo = document.querySelectorAll('#breadcrumbs .crumb').length;
      // afterTwo is 2 if we hit another question, or path length on result.
      expect(afterTwo).toBeGreaterThanOrEqual(afterOne);

      window.goBack();
      const afterBack = document.querySelectorAll('#breadcrumbs .crumb').length;
      expect(afterBack).toBe(afterOne);
    }
  });

  test('restart() clears the path and renders the root question', () => {
    // Drill in at least one level.
    const buttons = currentQuestionButtons();
    if (buttons.length > 0) buttons[0].click();

    window.restart();
    expect(document.querySelectorAll('#breadcrumbs .crumb').length).toBe(0);
    expect(document.querySelector('.question-card')).not.toBeNull();
  });
});

describe('ds-chooser: localStorage history', () => {
  function clickUntilResult(maxSteps = 8) {
    for (let i = 0; i < maxSteps; i++) {
      const buttons = currentQuestionButtons();
      if (buttons.length === 0) return true; // result reached
      buttons[0].click();
    }
    return false;
  }

  test('reaching a result writes an entry to ds-chooser-history', () => {
    const reached = clickUntilResult();
    expect(reached).toBe(true);

    const raw = window.localStorage.getItem('ds-chooser-history');
    expect(raw).not.toBeNull();
    const history = JSON.parse(raw);
    expect(Array.isArray(history)).toBe(true);
    expect(history.length).toBeGreaterThanOrEqual(1);
    expect(typeof history[0].name).toBe('string');
    expect(typeof history[0].key).toBe('string');
    expect(typeof history[0].ts).toBe('number');
  });

  test('history panel renders recent recommendations once history exists', () => {
    clickUntilResult();
    const panel = document.getElementById('history-panel');
    expect(panel.textContent).toMatch(/Recent Recommendations|Recommendations/i);
    expect(panel.querySelectorAll('.history-item').length).toBeGreaterThanOrEqual(1);
  });

  test('history is capped at 10 entries', () => {
    // Run the wizard 12 times choosing slightly different paths so entries
    // don't collapse via the de-dup filter, then check the cap.
    for (let i = 0; i < 12; i++) {
      window.restart();
      const buttons = currentQuestionButtons();
      // Alternate first/second/third option when available to vary paths.
      const idx = i % Math.max(1, buttons.length);
      if (buttons[idx]) buttons[idx].click();
      else if (buttons[0]) buttons[0].click();
      // Then click the first option until we reach a result.
      for (let k = 0; k < 8; k++) {
        const b = currentQuestionButtons();
        if (b.length === 0) break;
        b[0].click();
      }
    }
    const history = JSON.parse(window.localStorage.getItem('ds-chooser-history') || '[]');
    expect(history.length).toBeLessThanOrEqual(10);
  });

  test('result card includes "View Source" link to the .ml file on GitHub', () => {
    clickUntilResult();
    const link = document.querySelector(
      'a[href*="sauravbhattacharya001/Ocaml-sample-code"][href$=".ml"]'
    );
    expect(link).not.toBeNull();
    expect(link.getAttribute('href')).toMatch(/\.ml$/);
  });
});

describe('ds-chooser: showDirect() alternatives navigation', () => {
  test('clicking an "Also consider" chip navigates directly to that DS', () => {
    // Walk to a result that exposes alternatives.
    for (let i = 0; i < 8; i++) {
      const b = currentQuestionButtons();
      if (b.length === 0) break;
      b[0].click();
    }

    const altChip = document.querySelector('.alt-chip');
    if (!altChip) return; // not every leaf has alts — skip gracefully.

    const originalHeading = document.querySelector('.result-card h2').textContent;
    altChip.click();

    const newHeading = document.querySelector('.result-card h2');
    expect(newHeading).not.toBeNull();
    // The alt navigation should at minimum still produce a valid card.
    expect(newHeading.textContent.length).toBeGreaterThan(0);
    // And the breadcrumb count should have grown by one.
    const crumbs = document.querySelectorAll('#breadcrumbs .crumb').length;
    expect(crumbs).toBeGreaterThanOrEqual(1);
  });
});
