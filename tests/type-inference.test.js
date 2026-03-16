/**
 * Tests for Type Inference Playground (docs/type-inference.html)
 * Run with: node tests/type-inference.test.js
 */

const fs = require('fs');
const path = require('path');

let passed = 0;
let failed = 0;

function assert(condition, msg) {
    if (condition) { passed++; console.log(`  ✅ ${msg}`); }
    else { failed++; console.error(`  ❌ ${msg}`); }
}

// Load the HTML
const html = fs.readFileSync(path.join(__dirname, '..', 'docs', 'type-inference.html'), 'utf8');

// Extract JS
const scriptMatch = html.match(/<script>([\s\S]*?)<\/script>/);
assert(!!scriptMatch, 'Script block exists');

const js = scriptMatch[1];

// Extract CHALLENGES array from script
const challengesMatch = js.match(/const CHALLENGES = \[([\s\S]*?)\];/);
assert(!!challengesMatch, 'CHALLENGES array found');

// Parse challenges by counting objects
const challengeBlocks = js.match(/\{\s*code:/g);
const challengeCount = challengeBlocks ? challengeBlocks.length : 0;
assert(challengeCount >= 30, `At least 30 challenges (found ${challengeCount})`);

// Check levels present
assert(js.includes("level: 'beginner'"), 'Has beginner challenges');
assert(js.includes("level: 'intermediate'"), 'Has intermediate challenges');
assert(js.includes("level: 'advanced'"), 'Has advanced challenges');

// Check each challenge has required fields
const requiredFields = ['code', 'answer', 'alts', 'hint', 'explanation', 'level'];
for (const field of requiredFields) {
    const regex = new RegExp(`${field}:`, 'g');
    const count = (js.match(regex) || []).length;
    assert(count >= challengeCount, `All challenges have '${field}' field (${count}/${challengeCount})`);
}

// Check UI elements
assert(html.includes('id="challengeCard"'), 'Challenge card element');
assert(html.includes('id="answerInput"'), 'Answer input element');
assert(html.includes('id="feedback"'), 'Feedback element');
assert(html.includes('id="summaryCard"'), 'Summary card element');
assert(html.includes('id="progressBar"'), 'Progress bar element');
assert(html.includes('id="scoreCorrect"'), 'Correct score display');
assert(html.includes('id="scoreWrong"'), 'Wrong score display');
assert(html.includes('id="streak"'), 'Streak display');

// Check functions
const functions = ['checkAnswer', 'showHint', 'revealAnswer', 'nextQuestion', 'filterPool', 'showQuestion', 'showSummary', 'normalize', 'shuffle'];
for (const fn of functions) {
    assert(js.includes(`function ${fn}`), `Function ${fn}() exists`);
}

// Check difficulty tabs
assert(html.includes('data-level="beginner"'), 'Beginner tab');
assert(html.includes('data-level="intermediate"'), 'Intermediate tab');
assert(html.includes('data-level="advanced"'), 'Advanced tab');
assert(html.includes('data-level="all"'), 'All tab');

// Check normalize function handles whitespace and parens
assert(js.includes('.replace(/\\s+/g'), 'normalize handles whitespace');
assert(js.includes(".replace(/[()]/g, '')"), 'normalize handles parentheses');

// Check Enter key handler
assert(js.includes("e.key === 'Enter'"), 'Enter key triggers check');

// Check sidebar nav link
assert(html.includes('type-inference.html'), 'Self-link in sidebar');
assert(html.includes('class="nav-link active"'), 'Active nav link');

// Check specific challenge types
assert(js.includes("'type error'"), 'Has type error challenge (self-application)');
assert(js.includes("fun f -> f f"), 'Has self-application challenge');
assert(js.includes("List.map"), 'Has List.map challenge');
assert(js.includes("List.fold_left"), 'Has List.fold_left challenge');

// Summary
console.log(`\n${passed + failed} tests: ${passed} passed, ${failed} failed`);
process.exit(failed > 0 ? 1 : 0);
