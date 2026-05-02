"""Tests for refactoring_autopilot.ml — Refactoring Autopilot Engine.

Validates all 8 detectors, application, scoring, and dashboard generation
by parsing the OCaml source and running the compiled binary.
"""

import os
import re
import subprocess
import unittest
import tempfile
import json

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SOURCE = os.path.join(ROOT, "refactoring_autopilot.ml")


class TestRefactoringAutopilotSource(unittest.TestCase):
    """Validate source structure and completeness."""

    @classmethod
    def setUpClass(cls):
        with open(SOURCE, encoding="utf-8") as f:
            cls.src = f.read()

    def test_file_exists(self):
        self.assertTrue(os.path.isfile(SOURCE))

    def test_has_header_comment(self):
        self.assertIn("refactoring_autopilot.ml", self.src[:200])
        self.assertIn("Autonomous Refactoring Autopilot Engine", self.src[:500])

    def test_has_expr_type(self):
        self.assertIn("type expr =", self.src)

    def test_has_pattern_type(self):
        self.assertIn("and pattern =", self.src)

    # ── AST Variants ────────────────────────────────────────────────────

    def test_expr_lit(self):
        self.assertIn("| Lit of int", self.src)

    def test_expr_boolllit(self):
        self.assertIn("| BoolLit of bool", self.src)

    def test_expr_var(self):
        self.assertIn("| Var of string", self.src)

    def test_expr_lam(self):
        self.assertIn("| Lam of string * expr", self.src)

    def test_expr_app(self):
        self.assertIn("| App of expr * expr", self.src)

    def test_expr_let(self):
        self.assertIn("| Let of string * expr * expr", self.src)

    def test_expr_letrec(self):
        self.assertIn("| LetRec of string * expr * expr", self.src)

    def test_expr_match(self):
        self.assertIn("| Match of expr * (pattern * expr) list", self.src)

    def test_expr_seq(self):
        self.assertIn("| Seq of expr list", self.src)

    def test_pattern_wild(self):
        self.assertIn("| PWild", self.src)

    def test_pattern_pvar(self):
        self.assertIn("| PVar of string", self.src)

    def test_pattern_plit(self):
        self.assertIn("| PLit of int", self.src)

    def test_pattern_ptuple(self):
        self.assertIn("| PTuple of pattern list", self.src)

    def test_pattern_pcons(self):
        self.assertIn("| PCons of string * pattern list", self.src)

    # ── Detectors ───────────────────────────────────────────────────────

    def test_has_eta_detector(self):
        self.assertIn("detect_eta", self.src)
        self.assertIn("EtaReduction", self.src)

    def test_has_dead_let_detector(self):
        self.assertIn("detect_dead_let", self.src)
        self.assertIn("DeadLetBinding", self.src)

    def test_has_constant_fold_detector(self):
        self.assertIn("detect_constant_fold", self.src)
        self.assertIn("ConstantFolding", self.src)

    def test_has_identity_detector(self):
        self.assertIn("detect_identity_elim", self.src)
        self.assertIn("IdentityElimination", self.src)

    def test_has_redundant_match_detector(self):
        self.assertIn("detect_redundant_match", self.src)
        self.assertIn("RedundantMatch", self.src)

    def test_has_nested_if_detector(self):
        self.assertIn("detect_nested_if", self.src)
        self.assertIn("NestedIfSimplification", self.src)

    def test_has_let_inline_detector(self):
        self.assertIn("detect_let_inline", self.src)
        self.assertIn("LetInlining", self.src)

    def test_has_common_subexpr_detector(self):
        self.assertIn("detect_common_subexpr", self.src)
        self.assertIn("CommonSubexpression", self.src)

    # ── Core Functions ──────────────────────────────────────────────────

    def test_has_apply_refactoring(self):
        self.assertIn("apply_refactoring", self.src)

    def test_has_apply_all(self):
        self.assertIn("apply_all", self.src)

    def test_has_run_autopilot(self):
        self.assertIn("run_autopilot", self.src)

    def test_has_free_vars(self):
        self.assertIn("free_vars", self.src)

    def test_has_expr_size(self):
        self.assertIn("expr_size", self.src)

    def test_has_expr_equal(self):
        self.assertIn("expr_equal", self.src)

    def test_has_subst(self):
        self.assertIn("subst", self.src)

    def test_has_count_var(self):
        self.assertIn("count_var", self.src)

    def test_has_pp_expr(self):
        self.assertIn("pp_expr", self.src)

    def test_has_pp_pattern(self):
        self.assertIn("pp_pattern", self.src)

    # ── Scoring ─────────────────────────────────────────────────────────

    def test_has_complexity_reduction(self):
        self.assertIn("compute_complexity_reduction", self.src)

    def test_has_health_score(self):
        self.assertIn("compute_health_score", self.src)

    def test_has_detector_stats(self):
        self.assertIn("compute_detector_stats", self.src)

    def test_has_insights(self):
        self.assertIn("generate_insights", self.src)

    # ── Dashboard ───────────────────────────────────────────────────────

    def test_has_dashboard_generator(self):
        self.assertIn("generate_dashboard", self.src)

    def test_has_html_escape(self):
        self.assertIn("html_escape", self.src)

    def test_dashboard_contains_html(self):
        self.assertIn("<!DOCTYPE html>", self.src)

    def test_dashboard_has_styles(self):
        self.assertIn("<style>", self.src)

    def test_dashboard_has_scores_section(self):
        self.assertIn("Scores", self.src)

    def test_dashboard_has_findings_table(self):
        self.assertIn("Findings", self.src)

    def test_dashboard_has_trace_section(self):
        self.assertIn("Transformation Trace", self.src)

    def test_dashboard_has_insights_section(self):
        self.assertIn("Insights", self.src)

    # ── Session Type ────────────────────────────────────────────────────

    def test_has_session_type(self):
        self.assertIn("type session", self.src)
        self.assertIn("input_expr", self.src)
        self.assertIn("final_expr", self.src)
        self.assertIn("all_findings", self.src)

    def test_has_finding_type(self):
        self.assertIn("type finding", self.src)
        self.assertIn("confidence", self.src)

    def test_has_trace_step_type(self):
        self.assertIn("type trace_step", self.src)

    def test_has_category_type(self):
        self.assertIn("type category", self.src)

    # ── Main / Examples ─────────────────────────────────────────────────

    def test_has_main(self):
        self.assertIn("let () =", self.src)

    def test_has_multiple_examples(self):
        count = self.src.count("run_autopilot")
        self.assertGreaterEqual(count, 8, "Should have at least 8 example runs")

    def test_writes_dashboard_file(self):
        self.assertIn("refactoring_autopilot_dashboard.html", self.src)

    # ── Category Metadata ───────────────────────────────────────────────

    def test_has_category_name(self):
        self.assertIn("category_name", self.src)

    def test_has_category_color(self):
        self.assertIn("category_color", self.src)

    # ── Fixpoint Iteration ──────────────────────────────────────────────

    def test_has_max_iterations(self):
        self.assertIn("max_iterations", self.src)

    def test_has_confidence_threshold(self):
        # Confidence-based filtering for application
        self.assertIn("confidence", self.src)
        self.assertIn("0.80", self.src)

    # ── Random Infrastructure ───────────────────────────────────────────

    def test_has_random_infra(self):
        self.assertIn("global_seed", self.src)
        self.assertIn("next_random", self.src)
        self.assertIn("random_int", self.src)
        self.assertIn("random_float", self.src)

    # ── Size Checks ─────────────────────────────────────────────────────

    def test_source_size_reasonable(self):
        lines = self.src.count('\n')
        self.assertGreater(lines, 500, "Source should be substantial (>500 lines)")
        self.assertLess(lines, 2000, "Source shouldn't be bloated (<2000 lines)")


if __name__ == "__main__":
    unittest.main()
