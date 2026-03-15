"""Tests for the Concept Map HTML page (docs/concept-map.html).

Validates structure, data integrity, and consistency with
the explorer's example database.
"""

import os
import re
import unittest


ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CONCEPT_MAP = os.path.join(ROOT, "docs", "concept-map.html")
EXPLORER = os.path.join(ROOT, "docs", "explorer.html")


def read_file(path):
    with open(path, encoding="utf-8") as f:
        return f.read()


def extract_example_names(html):
    """Extract example name strings from the EXAMPLES array."""
    return re.findall(r'name:\s*"([^"]+)"', html)


class TestConceptMap(unittest.TestCase):
    """Validate concept-map.html structure and data."""

    @classmethod
    def setUpClass(cls):
        cls.html = read_file(CONCEPT_MAP)

    def test_file_exists(self):
        self.assertTrue(os.path.isfile(CONCEPT_MAP))

    def test_has_canvas_element(self):
        self.assertIn('<canvas id="graph"', self.html)

    def test_has_examples_data(self):
        self.assertIn("const EXAMPLES", self.html)

    def test_has_learning_paths(self):
        self.assertIn("const LEARNING_PATHS", self.html)

    def test_has_category_colors(self):
        self.assertIn("const CATEGORY_COLORS", self.html)

    def test_example_count_matches_explorer(self):
        map_names = set(extract_example_names(self.html))
        explorer_html = read_file(EXPLORER)
        explorer_names = set(extract_example_names(explorer_html))
        self.assertEqual(map_names, explorer_names,
                         f"Mismatch: in map not explorer={map_names - explorer_names}, "
                         f"in explorer not map={explorer_names - map_names}")

    def test_all_examples_have_concepts(self):
        # Every example entry should have a concepts array
        entries = re.findall(r'\{[^}]*name:\s*"[^"]+"[^}]*\}', self.html)
        for entry in entries:
            if 'concepts:' not in entry:
                name = re.search(r'name:\s*"([^"]+)"', entry)
                self.fail(f"Example {name.group(1) if name else '?'} missing concepts array")

    def test_learning_paths_reference_valid_examples(self):
        map_names = set(extract_example_names(self.html))
        path_refs = re.findall(r'"([\w_]+)"', 
                               re.search(r'const LEARNING_PATHS\s*=\s*\{(.+?)\};',
                                         self.html, re.DOTALL).group(1))
        # Filter to only strings that look like example names (lowercase with underscores)
        path_refs = [r for r in path_refs if r.islower() or '_' in r]
        # Exclude path names like "Data Structures" etc
        path_refs = [r for r in path_refs if ' ' not in r and len(r) > 2]
        for ref in path_refs:
            self.assertIn(ref, map_names, f"Learning path references unknown example: {ref}")

    def test_has_filter_buttons(self):
        self.assertIn('data-filter="all"', self.html)
        self.assertIn('data-filter="data-structures"', self.html)
        self.assertIn('data-filter="algorithms"', self.html)

    def test_has_info_panel(self):
        self.assertIn('id="info-panel"', self.html)

    def test_has_tooltip(self):
        self.assertIn('id="tooltip"', self.html)

    def test_has_sidebar_nav_link(self):
        self.assertIn('concept-map.html', self.html)

    def test_has_force_graph_class(self):
        self.assertIn('class ForceGraph', self.html)

    def test_no_xss_in_template(self):
        self.assertIn('escapeHtml', self.html)


if __name__ == "__main__":
    unittest.main()
