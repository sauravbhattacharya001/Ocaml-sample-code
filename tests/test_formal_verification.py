"""Tests for formal_verification.ml — Formal Verification Engine.

Validates all 7 engines, WP calculus, VC generation/checking, invariant
inference, program analysis, orchestration, and dashboard generation
by parsing the OCaml source structure.
"""

import os
import re
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SOURCE = os.path.join(ROOT, "formal_verification.ml")


class TestFormalVerificationSource(unittest.TestCase):
    """Validate source structure and completeness."""

    @classmethod
    def setUpClass(cls):
        with open(SOURCE, encoding="utf-8") as f:
            cls.src = f.read()

    def test_file_exists(self):
        self.assertTrue(os.path.isfile(SOURCE))

    def test_has_header_comment(self):
        self.assertIn("formal_verification.ml", self.src[:200])

    def test_has_description(self):
        self.assertIn("Formal Verification Engine", self.src[:500])

    def test_has_hoare_logic_mention(self):
        self.assertIn("Hoare", self.src)

    def test_has_weakest_precondition_mention(self):
        self.assertIn("weakest precondition", self.src.lower())


class TestExpressionTypes(unittest.TestCase):
    """Validate expression and statement type definitions."""

    @classmethod
    def setUpClass(cls):
        with open(SOURCE, encoding="utf-8") as f:
            cls.src = f.read()

    def test_has_binop_type(self):
        self.assertIn("type binop", self.src)

    def test_has_cmpop_type(self):
        self.assertIn("type cmpop", self.src)

    def test_has_expr_type(self):
        self.assertIn("type expr", self.src)

    def test_has_bexpr_type(self):
        self.assertIn("type bexpr", self.src)

    def test_has_stmt_type(self):
        self.assertIn("type stmt", self.src)

    def test_has_prop_type(self):
        self.assertRegex(self.src, r"and prop\s*=|type prop\s*=")

    def test_has_skip_constructor(self):
        self.assertIn("SSkip", self.src)

    def test_has_assign_constructor(self):
        self.assertIn("SAssign", self.src)

    def test_has_seq_constructor(self):
        self.assertIn("SSeq", self.src)

    def test_has_if_constructor(self):
        self.assertIn("SIf", self.src)

    def test_has_while_constructor(self):
        self.assertIn("SWhile", self.src)

    def test_has_assert_constructor(self):
        self.assertIn("SAssert", self.src)

    def test_binop_variants(self):
        for op in ["Add", "Sub", "Mul", "Div", "Mod"]:
            self.assertIn(op, self.src, f"Missing binop variant: {op}")

    def test_cmpop_variants(self):
        for op in ["Eq", "Ne", "Lt", "Le", "Gt", "Ge"]:
            self.assertIn(op, self.src, f"Missing cmpop variant: {op}")


class TestWPCalculator(unittest.TestCase):
    """Validate WP Calculator (Engine 1)."""

    @classmethod
    def setUpClass(cls):
        with open(SOURCE, encoding="utf-8") as f:
            cls.src = f.read()

    def test_module_exists(self):
        self.assertIn("module WPCalculator", self.src)

    def test_has_compute_function(self):
        self.assertRegex(self.src, r"let rec compute")

    def test_handles_skip(self):
        self.assertIn("SSkip", self.src)

    def test_handles_assign(self):
        self.assertIn("SAssign", self.src)

    def test_handles_seq(self):
        self.assertIn("SSeq", self.src)

    def test_handles_if(self):
        self.assertIn("SIf", self.src)

    def test_handles_while(self):
        self.assertIn("SWhile", self.src)

    def test_substitution_function(self):
        self.assertIn("prop_subst", self.src)

    def test_wp_result_type(self):
        self.assertIn("wp_prop", self.src)
        self.assertIn("wp_vcs", self.src)


class TestVCGenerator(unittest.TestCase):
    """Validate VC Generator (Engine 2)."""

    @classmethod
    def setUpClass(cls):
        with open(SOURCE, encoding="utf-8") as f:
            cls.src = f.read()

    def test_module_exists(self):
        self.assertIn("module VCGenerator", self.src)

    def test_has_generate_function(self):
        self.assertIn("let generate", self.src)

    def test_has_labeled_vcs(self):
        self.assertIn("generate_labeled", self.src)

    def test_vc_origin_types(self):
        for origin in ["VCPrecondition", "VCInvariantInit", "VCInvariantPreservation",
                        "VCLoopExit", "VCPostcondition", "VCAssertion"]:
            self.assertIn(origin, self.src, f"Missing VC origin: {origin}")

    def test_vc_has_id(self):
        self.assertIn("vc_id", self.src)

    def test_vc_has_label(self):
        self.assertIn("vc_label", self.src)


class TestVCChecker(unittest.TestCase):
    """Validate VC Checker (Engine 3)."""

    @classmethod
    def setUpClass(cls):
        with open(SOURCE, encoding="utf-8") as f:
            cls.src = f.read()

    def test_module_exists(self):
        self.assertIn("module VCChecker", self.src)

    def test_has_check_function(self):
        self.assertIn("check_vc", self.src)

    def test_has_check_all(self):
        self.assertIn("check_all", self.src)

    def test_has_simplification(self):
        self.assertIn("simplify_prop", self.src)

    def test_has_counterexample_search(self):
        self.assertIn("counterexample", self.src)

    def test_status_types(self):
        self.assertIn("VCValid", self.src)
        self.assertIn("VCInvalid", self.src)
        self.assertIn("VCUnknown", self.src)

    def test_gen_valuations(self):
        self.assertIn("gen_valuations", self.src)


class TestInvariantInference(unittest.TestCase):
    """Validate Invariant Inference (Engine 4)."""

    @classmethod
    def setUpClass(cls):
        with open(SOURCE, encoding="utf-8") as f:
            cls.src = f.read()

    def test_module_exists(self):
        self.assertIn("module InvariantInference", self.src)

    def test_has_infer_function(self):
        self.assertIn("let infer", self.src)

    def test_strategy_constant_propagation(self):
        self.assertIn("constant_propagation", self.src)

    def test_strategy_bound_inference(self):
        self.assertIn("bound_inference", self.src)

    def test_strategy_relationship_inference(self):
        self.assertIn("relationship_inference", self.src)

    def test_strategy_postcondition_weakening(self):
        self.assertIn("postcondition_weakening", self.src)

    def test_candidate_has_confidence(self):
        self.assertIn("inv_confidence", self.src)

    def test_candidate_has_strategy(self):
        self.assertIn("inv_strategy", self.src)

    def test_candidate_has_description(self):
        self.assertIn("inv_description", self.src)


class TestProgramAnalyzer(unittest.TestCase):
    """Validate Program Analyzer (Engine 5)."""

    @classmethod
    def setUpClass(cls):
        with open(SOURCE, encoding="utf-8") as f:
            cls.src = f.read()

    def test_module_exists(self):
        self.assertIn("module ProgramAnalyzer", self.src)

    def test_has_analyze_function(self):
        self.assertIn("let analyze", self.src)

    def test_has_complexity_calculation(self):
        self.assertIn("stmt_complexity", self.src)

    def test_has_loop_counting(self):
        self.assertIn("count_loops", self.src)

    def test_has_branch_counting(self):
        self.assertIn("count_branches", self.src)

    def test_has_termination_detection(self):
        self.assertIn("detect_termination", self.src)

    def test_analysis_result_fields(self):
        for field in ["variables", "assigned", "complexity", "has_loops",
                       "loop_count", "branch_count", "assert_count", "termination_hint"]:
            self.assertIn(field, self.src, f"Missing analysis field: {field}")


class TestOrchestrator(unittest.TestCase):
    """Validate Verification Orchestrator (Engine 6)."""

    @classmethod
    def setUpClass(cls):
        with open(SOURCE, encoding="utf-8") as f:
            cls.src = f.read()

    def test_module_exists(self):
        self.assertIn("module Orchestrator", self.src)

    def test_has_verify_function(self):
        self.assertIn("let verify", self.src)

    def test_counts_invariants(self):
        self.assertIn("count_invariants", self.src)

    def test_annotates_missing_invariants(self):
        self.assertIn("annotate_invariants", self.src)

    def test_health_scoring(self):
        self.assertIn("health_score", self.src)

    def test_verdict_types(self):
        self.assertIn("Verified", self.src)
        self.assertIn("Failed", self.src)
        self.assertIn("Partial", self.src)

    def test_returns_insights(self):
        self.assertIn("insights", self.src)


class TestInsightGenerator(unittest.TestCase):
    """Validate Insight Generator (Engine 7)."""

    @classmethod
    def setUpClass(cls):
        with open(SOURCE, encoding="utf-8") as f:
            cls.src = f.read()

    def test_module_exists(self):
        self.assertIn("module InsightGenerator", self.src)

    def test_has_generate_function(self):
        self.assertIn("module InsightGenerator", self.src)
        self.assertIn("let generate result analysis", self.src)

    def test_complexity_insights(self):
        self.assertIn("High program complexity", self.src)

    def test_loop_insights(self):
        self.assertIn("Multiple loops", self.src)

    def test_scoring_insights(self):
        self.assertIn("Perfect score", self.src)


class TestDemoPrograms(unittest.TestCase):
    """Validate built-in demo programs."""

    @classmethod
    def setUpClass(cls):
        with open(SOURCE, encoding="utf-8") as f:
            cls.src = f.read()

    def test_module_exists(self):
        self.assertIn("module DemoPrograms", self.src)

    def test_has_square_program(self):
        self.assertIn("square_program", self.src)

    def test_has_division_program(self):
        self.assertIn("division_program", self.src)

    def test_has_factorial_program(self):
        self.assertIn("factorial_program", self.src)

    def test_has_max_program(self):
        self.assertIn("max_program", self.src)

    def test_has_sum_program(self):
        self.assertIn("sum_program", self.src)

    def test_has_swap_program(self):
        self.assertIn("swap_program", self.src)

    def test_has_all_demos_list(self):
        self.assertIn("all_demos", self.src)

    def test_at_least_5_demos(self):
        count = self.src.count("_program = {")
        self.assertGreaterEqual(count, 5, f"Expected >= 5 demo programs, found {count}")


class TestParser(unittest.TestCase):
    """Validate IMP program parser."""

    @classmethod
    def setUpClass(cls):
        with open(SOURCE, encoding="utf-8") as f:
            cls.src = f.read()

    def test_module_exists(self):
        self.assertIn("module Parser", self.src)

    def test_has_tokenizer(self):
        self.assertIn("tokenize", self.src)

    def test_has_parse_program(self):
        self.assertIn("parse_program", self.src)

    def test_has_parse_expr(self):
        self.assertIn("parse_expr", self.src)

    def test_has_parse_bexpr(self):
        self.assertIn("parse_bexpr", self.src)

    def test_has_parse_stmt(self):
        self.assertIn("parse_stmt", self.src)

    def test_has_parse_prop(self):
        self.assertIn("parse_prop", self.src)

    def test_token_types(self):
        for tok in ["TInt", "TId", "TLParen", "TRParen", "TLBrace", "TRBrace",
                     "TAssign", "TWhile", "TIf", "TElse", "TInv", "TAssert"]:
            self.assertIn(tok, self.src, f"Missing token type: {tok}")


class TestDashboard(unittest.TestCase):
    """Validate HTML dashboard generator."""

    @classmethod
    def setUpClass(cls):
        with open(SOURCE, encoding="utf-8") as f:
            cls.src = f.read()

    def test_module_exists(self):
        self.assertIn("module Dashboard", self.src)

    def test_has_generate_function(self):
        self.assertIn("module Dashboard", self.src)
        self.assertIn("let generate results", self.src)

    def test_generates_html(self):
        self.assertIn("DOCTYPE html", self.src)

    def test_has_health_gauge(self):
        self.assertIn("health-gauge", self.src)

    def test_has_vc_table(self):
        self.assertIn("<table>", self.src)

    def test_has_badges(self):
        self.assertIn("badge valid", self.src)
        self.assertIn("badge invalid", self.src)
        self.assertIn("badge unknown", self.src)

    def test_has_insights_section(self):
        self.assertIn("insight", self.src)


class TestCLIInterface(unittest.TestCase):
    """Validate CLI command-line interface."""

    @classmethod
    def setUpClass(cls):
        with open(SOURCE, encoding="utf-8") as f:
            cls.src = f.read()

    def test_has_main_entrypoint(self):
        self.assertIn("let () =", self.src)

    def test_has_demo_mode(self):
        self.assertIn("--demo", self.src)

    def test_has_verify_mode(self):
        self.assertIn("--verify", self.src)

    def test_has_dashboard_mode(self):
        self.assertIn("--dashboard", self.src)

    def test_has_usage_help(self):
        self.assertIn("Usage:", self.src)


class TestSubstitution(unittest.TestCase):
    """Validate expression/proposition substitution."""

    @classmethod
    def setUpClass(cls):
        with open(SOURCE, encoding="utf-8") as f:
            cls.src = f.read()

    def test_expr_subst(self):
        self.assertIn("expr_subst", self.src)

    def test_bexpr_subst(self):
        self.assertIn("bexpr_subst", self.src)

    def test_prop_subst(self):
        self.assertIn("prop_subst", self.src)


class TestEvaluation(unittest.TestCase):
    """Validate expression/proposition evaluation."""

    @classmethod
    def setUpClass(cls):
        with open(SOURCE, encoding="utf-8") as f:
            cls.src = f.read()

    def test_eval_expr(self):
        self.assertIn("eval_expr", self.src)

    def test_eval_bexpr(self):
        self.assertIn("eval_bexpr", self.src)

    def test_eval_prop(self):
        self.assertIn("eval_prop", self.src)

    def test_eval_binop(self):
        self.assertIn("eval_binop", self.src)

    def test_eval_cmpop(self):
        self.assertIn("eval_cmpop", self.src)


class TestPrettyPrinting(unittest.TestCase):
    """Validate pretty printing functions."""

    @classmethod
    def setUpClass(cls):
        with open(SOURCE, encoding="utf-8") as f:
            cls.src = f.read()

    def test_expr_to_string(self):
        self.assertIn("expr_to_string", self.src)

    def test_bexpr_to_string(self):
        self.assertIn("bexpr_to_string", self.src)

    def test_prop_to_string(self):
        self.assertIn("prop_to_string", self.src)

    def test_stmt_to_string(self):
        self.assertIn("stmt_to_string", self.src)

    def test_vc_origin_to_string(self):
        self.assertIn("vc_origin_to_string", self.src)

    def test_verdict_to_string(self):
        self.assertIn("verdict_to_string", self.src)


class TestSourceQuality(unittest.TestCase):
    """Validate overall source quality."""

    @classmethod
    def setUpClass(cls):
        with open(SOURCE, encoding="utf-8") as f:
            cls.src = f.read()

    def test_minimum_length(self):
        self.assertGreater(len(self.src), 20000, "Source too short for a complete engine")

    def test_no_todo_markers(self):
        self.assertNotIn("TODO", self.src)

    def test_no_fixme_markers(self):
        self.assertNotIn("FIXME", self.src)

    def test_balanced_parens(self):
        opens = self.src.count("(")
        closes = self.src.count(")")
        self.assertEqual(opens, closes, f"Unbalanced parentheses: {opens} opens, {closes} closes")

    def test_seven_modules(self):
        modules = re.findall(r"module\s+\w+", self.src)
        unique_modules = set(modules)
        # At least 7 modules (WPCalculator, VCGenerator, VCChecker, InvariantInference,
        # ProgramAnalyzer, Orchestrator, InsightGenerator, DemoPrograms, Dashboard, Parser)
        self.assertGreaterEqual(len(unique_modules), 7,
                                f"Expected >= 7 modules, found {len(unique_modules)}: {unique_modules}")

    def test_hoare_triple_type(self):
        self.assertIn("hoare_triple", self.src)

    def test_verification_result_type(self):
        self.assertIn("verification_result", self.src)


if __name__ == "__main__":
    unittest.main()
