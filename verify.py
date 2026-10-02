#!/usr/bin/env python3
"""Force a complete Lean rebuild and audit, using this project's pinned Lake environment.

Requires Python 3.9+, Git, and Lake/elan on PATH. Prepare dependencies with
`lake exe cache get`, then run `python3 verify.py`. No prior verification or
local .olean is reused: every local module is compiled after its dependencies.
Use `--jobs N` for at most N independent compiler processes (default: 1).
Logs and the machine-readable report go under verification/ by default.
"""

import argparse
import concurrent.futures
import datetime
import hashlib
import heapq
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time


MATHLIB_PIN = "db584cd6d46c92f209a44c0f1c829460d327499d"
TOOLCHAIN_PIN = "leanprover/lean4:v4.33.0"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
CONFIG_FILES = ("lean-toolchain", "lake-manifest.json", "lakefile.toml", "verify.py")
MILESTONES = {
    'manuscript_corollary_3_6_verified':
        ('CRGZeroDistributionCorollary.lean', 'CRGZeroDistributionCorollary.corollary_3_6'),
    'real_order_indicator_pairs_verified':
        ('CRGZeroDistributionRealPairs.lean', 'CRGZeroDistributionRealPairs.finite_real_solution_indicator_pairs'),
    'manuscript_proposition_5_1_verified':
        ('CRGPuiseuxProposition.lean', 'CRGPuiseuxProposition.proposition_5_1'),
    'manuscript_corollary_5_2_verified':
        ('CRGLinearKernelConclusion.lean', 'CRGLinearKernel.corollary_5_2'),
    'manuscript_corollary_5_3_verified':
        ('CRGPolynomialKernelConclusion.lean', 'CRGPolynomialKernel.corollary_5_3'),
    'constant_order_radial_levin_verified':
        ('LevinGeneral.lean', 'LevinGeneral.constantOrderRadialLevin'),
    'radial_levin_with_indicator_verified':
        ('LevinCriterion.lean', 'LevinCriterion.constantOrderRadialIndicatorLevin'),
    'radial_to_c0_bridge_verified':
        ('LevinC0.lean', 'LevinC0.diskRegular_of_radialRegular'),
    'full_constant_order_levin_criterion_verified':
        ('LevinC0.lean', 'LevinC0.constantOrderLevin'),
    'diagonal_rational_normal_form_verified':
        ('WasowDiagonal.lean', 'WasowDiagonal.diagonal_rational_normal_form'),
    'scalar_rational_normal_form_verified':
        ('WasowDiagonal.lean', 'WasowDiagonal.scalar_rational_normal_form'),
    'mixed_volterra_ode_bridge_verified':
        ('WasowVolterra.lean', 'WasowVolterra.exists_phase_difference_column_ode'),
    'mixed_volterra_fundamental_matrix_verified':
        ('WasowFundamental.lean', 'WasowFundamental.exists_fundamental_matrix'),
    'nilpotent_block_sylvester_step_verified':
        ('WasowFormalSylvester.lean', 'WasowFormalSylvester.exists_block_coefficient'),
    'constant_matrix_power_polynomial_bounds_verified':
        ('WasowRegularSingular.lean', 'WasowRegularSingular.exists_polynomial_bounds'),
    'normalized_matrix_inverse_bounds_verified':
        ('WasowMatrixBounds.lean', 'WasowMatrixBounds.eventually_uniform_mulVec_bounds'),
    'all_order_eigenblock_formal_reduction_verified':
        ('WasowFormalSeries.lean', 'WasowFormalSeries.exists_multiblock_powerSeries'),
    'all_order_nilpotent_row_formal_reduction_verified':
        ('WasowFormalSeries.lean', 'WasowFormalSeries.exists_multishift_powerSeries'),
    'formal_truncation_residual_verified':
        ('WasowTruncation.lean', 'WasowTruncation.defect_divisible'),
    'rational_shearing_identity_verified':
        ('WasowShearing.lean', 'WasowShearing.rational_transformed_coefficient'),
    'rational_ramification_verified':
        ('WasowRamification.lean', 'WasowRamification.eval_rationalCoefficient'),
    'actual_analytic_remainder_tail_verified':
        ('WasowAnalyticRemainder.lean', 'WasowAnalyticRemainder.exists_small_integrable_inverse_tail'),
    'approximate_to_exact_rayGauge_verified':
        ('WasowRealization.lean', 'WasowRealization.exists_exact_rayGauge'),
    'book_lemma_unnormalized_uniqueness_counterexample_verified':
        ('WasowBookCheck.lean', 'WasowBookCheck.not_existsUnique_unnormalized_last_row'),
    'normalized_lemma_19_1_verified':
        ('WasowNormalizedLemma.lean', 'WasowNormalizedLemma.existsUnique_normalized_lemma_19_1'),
    'normalized_multishift_formal_uniqueness_verified':
        ('WasowNormalizedRecurrence.lean', 'WasowNormalizedRecurrence.existsUnique_normalized_multishift_powerSeries'),
    'arbitrary_leading_matrix_block_basis_verified':
        ('WasowLeadingBlocks.lean', 'WasowLeadingBlocks.matrixCoordinates_leading'),
    'arbitrary_matrix_formal_eigenblock_reduction_verified':
        ('WasowArbitraryFormalBlocks.lean', 'WasowArbitraryFormalBlocks.exists_arbitrary_formal_block_reduction'),
    'actual_finite_truncation_residual_bound_verified':
        ('WasowActualTruncation.lean', 'WasowActualTruncation.actualDefect_isBigO'),
    'actual_finite_gauge_inverse_bounds_verified':
        ('WasowTruncatedGauge.lean', 'WasowTruncatedGauge.exists_inverse_tail_bounds'),
    'actual_raw_residual_small_tail_verified':
        ('WasowActualTail.lean', 'WasowActualTail.actualDefect_small_inverse_tail'),
    'sorted_nilpotent_jordan_coordinates_verified':
        ('WasowSortedJordan.lean', 'WasowSortedJordan.exists_sorted_jordan_matrix_coordinates'),
    'single_eigen_actual_shearing_step_wellFounded_verified':
        ('WasowShearingTermination.lean', 'WasowShearingTermination.step_wellFounded'),
    'actual_shearing_successor_coordinates_verified':
        ('WasowShearingTermination.lean', 'WasowShearingTermination.exists_successor'),
    'analytic_gauge_composition_closure_verified':
        ('WasowGaugeComposition.lean', 'WasowGaugeComposition.pullback_rayGauge'),
    'actual_constant_coordinate_gauge_pullback_verified':
        ('WasowGaugeComposition.lean', 'WasowGaugeComposition.pullback_constant_rayGauge'),
    'actual_integer_shearing_gauge_pullback_verified':
        ('WasowShearingGauge.lean', 'WasowShearingGauge.pullback_shearing_rayGauge'),
    'phase_family_zero_constant_normalization_verified':
        ('WasowPhaseNormalization.lean', 'WasowPhaseNormalization.normalize_phase_family'),
    'actual_matrix_rank_reduction_wellFounded_verified':
        ('WasowReductionTermination.lean', 'WasowReductionTermination.combinedStep_wellFounded'),
    'actual_formal_shearing_clear_powers_verified':
        ('WasowFormalShearing.lean', 'WasowFormalShearing.ramifiedSeries_clear_powers'),
    'actual_ramified_formal_leading_coefficient_verified':
        ('WasowFormalShearing.lean', 'WasowFormalShearing.constantCoeff_ramifiedSeries'),
    'actual_minimal_ramification_successor_verified':
        ('WasowRankSelection.lean', 'WasowRankSelection.exists_ramified_successor'),
    'general_jordan_basis_verified':
        ('WasowJordanBasis.lean', 'WasowJordanBasis.exists_generalized_jordan_basis'),
    'single_eigenvalue_jordan_formal_normalization_verified':
        ('WasowJordanFormal.lean', 'WasowJordanFormal.exists_single_eigenvalue_normalization'),
    'actual_pencil_strict_degree_descent_verified':
        ('WasowPencilDescent.lean', 'WasowPencilDescent.pencil_degreeMass_strict_drop'),
    'actual_shearing_slope_selection_verified':
        ('WasowShearingExceptional.lean', 'WasowShearingExceptional.exists_slope_integral_or_exceptional'),
    'single_eigenvalue_block_similarity_verified':
        ('WasowSingleEigenBlocks.lean', 'WasowSingleEigenBlocks.exists_shift_diagonal_similarity'),
    'puiseux_phase_tail_ordering_verified':
        ('WasowPhaseOrdering.lean', 'WasowPhaseOrdering.exists_common_phase_ordering'),
    'actual_weighted_regular_truncation_realization_verified':
        ('WasowRegularTruncation.lean', 'WasowRegularTruncation.exists_exact_rayGauge_of_regular_formal_truncation'),
    'actual_ramified_gauge_descent_verified':
        ('WasowRamifiedGauge.lean', 'WasowRamifiedGauge.descend_rayGauge'),
    'ramified_canonical_formal_data_to_original_gauge_verified':
        ('WasowAnalyticAssembly.lean', 'WasowAnalyticAssembly.exists_original_rayGauge_of_ramified_formal_truncation'),
    'general_shearing_termination_verified':
        ('WasowRecursiveTree.lean', 'WasowRecursiveTree.exists_reduction'),
    'actual_full_series_recursive_reduction_verified':
        ('WasowRecursiveTree.lean', 'WasowRecursiveTree.exists_reduction'),
    'actual_recursive_tree_fixed_phase_family_verified':
        ('WasowRecursivePhases.lean', 'WasowRecursivePhases.exists_reduction_fixed_phases'),
    'rational_analytic_expansion_verified':
        ('WasowRationalAtInfinity.lean', 'WasowRationalAtInfinity.exists_formal_expansion'),
    'rational_ray_analytic_expansion_verified':
        ('WasowRationalAtInfinity.lean', 'WasowRationalAtInfinity.exists_ray_expansion'),
    'rational_input_recursive_fixed_phases_verified':
        ('WasowRationalReduction.lean', 'WasowRationalReduction.exists_rational_reduction_fixed_phases'),
    'continuous_linear_ode_halfline_existence_verified':
        ('WasowFuchsianODE.lean', 'WasowFuchsianODE.exists_solution_Ici'),
    'general_fuchsian_rayGauge_verified':
        ('WasowFuchsian.lean', 'WasowFuchsian.exists_fuchsian_rayGauge'),
    'proper_rational_normal_form_verified':
        ('WasowFuchsian.lean', 'WasowFuchsian.proper_rational_normal_form'),
    'formal_regular_leaf_finite_truncation_verified':
        ('WasowFuchsianTruncation.lean', 'WasowFuchsianTruncation.exists_truncated_fundamental'),
    'regular_leaf_uniform_growth_exponent_verified':
        ('WasowRegularLeaf.lean', 'WasowRegularLeaf.exists_uniform_regular_exponent'),
    'general_polynomial_gauge_small_tail_verified':
        ('WasowPolynomialTail.lean', 'WasowPolynomialTail.exists_small_conjugated_tail'),
    'variable_regular_canonical_data_realization_verified':
        ('WasowFuchsianRealization.lean', 'WasowFuchsianRealization.exists_exact_rayGauge_of_fuchsian_formal_truncation'),
    'actual_fixed_phase_block_assembly_verified':
        ('WasowPhaseFamilyBlocks.lean', 'WasowPhaseFamilyBlocks.block_family_assembly'),
    'uniform_regular_block_gauge_verified':
        ('WasowRegularBlocks.lean', 'WasowRegularBlocks.exists_uniform_block_regularGauge'),
    'complete_regular_blocks_canonical_realization_verified':
        ('WasowRegularBlocks.lean', 'WasowRegularBlocks.exists_exact_rayGauge_of_regular_blocks'),
    'fixed_series_ray_rotation_verified':
        ('WasowRayRotation.lean', 'WasowRayRotation.rational_ray_expansion_from_fixed'),
    'formal_gauge_ray_rotation_verified':
        ('WasowRayRotation.lean', 'WasowRayRotation.rotate_gauge_equation'),
    'laurent_gauge_equation_composition_verified':
        ('WasowLaurentGauge.lean', 'WasowLaurentGauge.gaugeEquation_comp'),
    'formal_to_analytic_coefficient_bridge_verified':
        ('WasowGlobalFiniteRealization.lean', 'WasowGlobalFiniteRealization.exists_rational_global_finite_realization'),
    'automatic_rational_global_finite_realization_verified':
        ('WasowGlobalFiniteRealization.lean', 'WasowGlobalFiniteRealization.exists_rational_global_finite_realization'),
    'actual_laurent_ray_chain_rule_verified':
        ('WasowLaurentRayEquation.lean', 'WasowLaurentRayEquation.finite_realization_on_ray'),
    'canonical_truncation_actual_phase_derivative_verified':
        ('WasowCanonicalPhaseEvaluation.lean', 'WasowCanonicalPhaseEvaluation.eval_trunc_canonical_derivative'),
    'canonical_truncation_retains_fixed_phase_verified':
        ('WasowCanonicalTruncation.lean', 'WasowCanonicalTruncation.eval_trunc_canonical'),
    'actual_laurent_ramification_chain_rule_verified':
        ('WasowLaurentRamification.lean', 'WasowLaurentRamification.derivative_ramify'),
    'actual_whole_tree_laurent_gauge_verified':
        ('WasowGlobalFormalTree.lean', 'WasowGlobalFormalTree.exists_global_realization'),
    'actual_square_global_formal_normal_form_verified':
        ('WasowGlobalFormalSquare.lean', 'WasowGlobalFormalSquare.exists_global_formal_normal_form'),
    'laurent_finite_truncation_inverse_verified':
        ('WasowLaurentInverse.lean', 'WasowLaurentInverse.eventually_inverse_bounds_of_laurent'),
    'laurent_pole_clearing_from_actual_equation_verified':
        ('WasowLaurentClearing.lean', 'WasowLaurentClearing.automatic_cleared_data'),
    'laurent_actual_inverse_normalized_residual_verified':
        ('WasowLaurentRemainder.lean', 'WasowLaurentRemainder.remainder_isBigO'),
    'laurent_actual_finite_gauge_realization_verified':
        ('WasowLaurentFiniteRealization.lean', 'WasowLaurentFiniteRealization.finite_realization'),
    'laurent_actual_residual_unit_ray_small_tail_verified':
        ('WasowLaurentFiniteRealization.lean', 'WasowLaurentFiniteRealization.residual_small_ray_tail'),
    'laurent_polynomial_conjugated_tail_verified':
        ('WasowLaurentConjugatedTail.lean', 'WasowLaurentConjugatedTail.exists_small_tail'),
    'analytic_power_substitution_prescribed_coefficients_verified':
        ('WasowAnalyticPowerPullback.lean', 'WasowAnalyticPowerPullback.analytic_formal_cleared_pullback'),
    'full_wasow_rational_ray_normal_form_verified':
        ('WasowRationalNormalForm.lean', 'WasowRationalNormalForm.rational_ray_normal_form'),
    'rational_normal_form_fixed_phases_before_all_directions_verified':
        ('WasowRationalNormalForm.lean', 'WasowRationalNormalForm.exists_fixed_phase_normal_form'),
    'automatic_global_exact_ray_realization_verified':
        ('WasowRationalNormalForm.lean', 'WasowRationalNormalForm.ramified_ray_normal_form'),
    'automatic_original_ray_normal_form_verified':
        ('WasowRationalNormalForm.lean', 'WasowRationalNormalForm.original_ray_normal_form'),
    'canonical_regular_gauge_preserves_phase_fibers_verified':
        ('WasowCanonicalRegularGauge.lean', 'WasowCanonicalRegularGauge.exists_uniform_regular_family'),
    'regular_fundamental_matrix_commutant_verified':
        ('WasowPhaseRegularGauge.lean', 'WasowPhaseRegularGauge.matrix_solutions_commute'),
    'actual_global_conjugated_residual_small_tail_verified':
        ('WasowGlobalConjugatedTail.lean', 'WasowGlobalConjugatedTail.smallConjugatedTails'),
    'actual_laurent_regular_volterra_assembly_verified':
        ('WasowLaurentExactAssembly.lean', 'WasowLaurentExactAssembly.exists_exact_rayGauge_of_laurent_regular'),
    'whole_theorem_1_1_verified':
        ('CRGTheorem11.lean', 'CRGTheorem11.theorem_1_1'),
    'gundersen_angular_derivatives_verified':
        ('GundersenTheorem.lean', 'GundersenTheorem.exists_null_exceptional_set'),
    'actual_exponential_polynomial_grouping_verified':
        ('CRGCollectedEquation.lean', 'CRGCollectedEquation.exists_collected_equation'),
    'actual_dominant_group_residual_verified':
        ('CRGCollectedResidual.lean', 'CRGCollectedResidual.exists_residual_control'),
    'actual_scalar_ray_comparison_verified':
        ('CRGCompanionComparison.lean', 'CRGCompanionComparison.scalar_ray_comparison'),
    'finite_phase_positive_rational_order_crg_verified':
        ('CRGFinitePhaseEndgame.lean', 'CRGFinitePhaseEndgame.complete_of_finite_phases'),
    'dense_ray_phragmen_lindelof_verified':
        ('CRGPhragmenRay.lean', 'CRGPhragmenRay.dense_eventual_finiteType'),
    'dense_ray_polynomial_growth_verified':
        ('CRGPhragmenPolynomialRay.lean', 'CRGPhragmenPolynomialRay.dense_eventual_polynomial_bound'),
}


MILESTONES.update({
    "whole_theorem_3_2_verified": ("CRGSection3Alignment.lean", "CRGSection3Alignment.theorem_3_2"),
    "whole_theorem_3_5_verified": ("CRGSection3Alignment.lean", "CRGSection3Alignment.theorem_3_5"),
    "uniform_sector_proposition_5_1_verified": ("CRGUniformSectorAlignment.lean", "CRGUniformSectorAlignment.proposition_5_1_uniform"),
})

class VerificationError(Exception):
    """A precondition or audit failed; the report must remain unsuccessful."""


def utc_now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def proof_code(source):
    """Mask nested comments and string literals, preserving line boundaries.

    This deliberately small lexer is for our import/audit/placeholder scanner,
    not a substitute for Lean's parser. In particular, comment markers inside
    strings must not hide proof commands that follow the string.
    """
    result = []
    i = 0
    depth = 0
    in_string = False
    while i < len(source):
        char = source[i]
        pair = source[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                result.append("  ")
                i += 2
            elif pair == "-/":
                depth -= 1
                result.append("  ")
                i += 2
            else:
                result.append("\n" if char == "\n" else " ")
                i += 1
        elif in_string:
            if char == "\\" and i + 1 < len(source):
                result.append(" \n" if source[i + 1] == "\n" else "  ")
                i += 2
            else:
                if char == '"':
                    in_string = False
                result.append("\n" if char == "\n" else " ")
                i += 1
        elif pair == "/-":
            depth = 1
            result.append("  ")
            i += 2
        elif pair == "--":
            end = source.find("\n", i)
            end = len(source) if end < 0 else end
            result.append(" " * (end - i))
            i = end
        elif char == '"':
            in_string = True
            result.append(" ")
            i += 1
        else:
            result.append(char)
            i += 1
    return "".join(result)


def source_metadata(source):
    code = proof_code(source)
    namespaces = set(re.findall(r"^\s*namespace\s+([\w.']+)\s*$", code, re.M))
    if len(namespaces) > 1:
        raise VerificationError("Audit name resolver requires one distinct namespace per source")
    namespace = next(iter(namespaces), "")
    expected = []
    for name in re.findall(r"^\s*#print\s+axioms\s+([\w.']+)\s*$", code, re.M):
        if namespace and not name.startswith(namespace + "."):
            name = namespace + "." + name
        expected.append(name)
    imports = []
    for line in re.findall(r"^\s*(?:public\s+)?import\s+([^\n]+)", code, re.M):
        imports.extend(line.split())
    forbidden = re.findall(r"\b(?:sorry|admit|axiom|native_decide)\b", code)
    return {"expected": expected, "imports": imports, "forbidden": forbidden}


def discover_sources(project):
    # This distribution uses one top-level .lean source per Lake library.
    return {p.stem: p for p in sorted(project.glob("*.lean")) if p.name != "lakefile.lean"}


def module_order(metadata):
    """Topologically sort local imports, rejecting cycles; audit the whole set last."""
    if "Audit" not in metadata:
        raise VerificationError("Audit.lean is required for the unified declaration check")
    order = []
    visiting = set()
    finished = set()

    def visit(module):
        if module in visiting:
            raise VerificationError("Local import cycle at " + module)
        if module in finished:
            return
        visiting.add(module)
        for dep in metadata[module]["imports"]:
            if dep in metadata:
                if dep == "Audit":
                    raise VerificationError("Proof modules must not import the unified Audit")
                visit(dep)
        visiting.remove(module)
        finished.add(module)
        order.append(module)

    for module in sorted(metadata):
        if module != "Audit":
            visit(module)
    visit("Audit")
    return order


def audit_output(output, expected):
    pairs = re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]", output, re.M)
    audits = {name: [item.strip() for item in axioms.split(",") if item.strip()]
              for name, axioms in pairs}
    names_match = (len(expected) == len(set(expected))
                   and len(pairs) == len(audits)
                   and set(expected) == set(audits))
    axioms_allowed = ("sorryAx" not in output
                      and "declaration uses 'sorry'" not in output
                      and all(set(axioms) <= ALLOWED_AXIOMS for axioms in audits.values()))
    return audits, names_match, axioms_allowed


def run_command(command, project, env):
    return subprocess.run(command, cwd=project, env=env, text=True,
                          encoding="utf-8", errors="replace", capture_output=True)


def checked_output(command, project, env):
    result = run_command(command, project, env)
    if result.returncode:
        detail = (result.stderr or result.stdout).strip()
        raise VerificationError("Command failed: " + " ".join(command) + "\n" + detail)
    return result.stdout.strip()


def check_dependencies(project, env):
    manifest = json.loads((project / "lake-manifest.json").read_text(encoding="utf-8"))
    mathlib = [p for p in manifest.get("packages", []) if p.get("name") == "mathlib"]
    if len(mathlib) != 1 or mathlib[0].get("rev") != MATHLIB_PIN:
        raise VerificationError("lake-manifest.json does not pin the required mathlib revision")
    if manifest.get("packagesDir") != ".lake/packages":
        raise VerificationError("Expected project-local dependency directory .lake/packages")
    package = ".lake/packages/mathlib"
    if not (project / package).is_dir():
        raise VerificationError("Mathlib is missing. Prepare dependencies with: lake exe cache get")
    revision = checked_output(["git", "-C", package, "rev-parse", "HEAD"], project, env)
    clean = not checked_output(["git", "-C", package, "status", "--porcelain"], project, env)
    if revision != MATHLIB_PIN:
        raise VerificationError("Project-local mathlib checkout has an unexpected revision")
    if not clean:
        raise VerificationError("Project-local mathlib source checkout is dirty")
    return revision, clean


def write_report(output_dir, report):
    temporary = output_dir / "verification.json.tmp"
    temporary.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    temporary.replace(output_dir / "verification.json")


def summarize(report, expected_files):
    entries = {entry["file"]: entry for entry in report["files"]}
    proved_names = set().union(*(set(entry["audits"]) for entry in report["files"]
                                if entry["file"] != "Audit.lean"))
    unified = entries.get("Audit.lean")
    report["distinct_proved_declarations"] = len(proved_names)
    report["unified_audit_matches_modules"] = bool(
        unified and unified["passed"] and set(unified["audits"]) == proved_names)
    report["all_modules_checked"] = set(entries) == set(expected_files)
    report["all_requested_checks_passed"] = bool(
        not report.get("error")
        and report["all_modules_checked"]
        and all(entry["passed"] for entry in entries.values())
        and report["unified_audit_matches_modules"]
        and report.get("all_sources_unchanged", False)
        and report.get("all_oleans_unchanged", False)
        and report.get("configuration_unchanged", False)
        and report.get("dependency_check_passed_at_end", False))
    # A milestone is certified only after the complete run has succeeded.
    for flag, (filename, declaration) in MILESTONES.items():
        entry = entries.get(filename)
        report[flag] = bool(report["all_requested_checks_passed"] and entry
                            and entry["passed"] and declaration in entry["audits"])
    report["warning_count"] = sum(entry["warning_count"] for entry in entries.values())


def compile_module(module, project, output_dir, sources, initial_bytes, metadata, env):
    """Freshly compile one module and return its complete audit record and log."""
    source = sources[module]
    source_bytes = initial_bytes[module]
    info = metadata[module]
    if source.read_bytes() != source_bytes:
        raise VerificationError(source.name + ": source changed since verification started")
    olean = Path(".lake") / "build" / "lib" / "lean" / (module + ".olean")
    target = project / olean
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.exists():
        target.unlink()
    command = ["lake", "env", "lean", "-o", olean.as_posix(), source.name]
    log = Path("modules") / (module + ".log")
    module_started = time.monotonic()
    result = run_command(command, project, env)
    output = result.stdout + result.stderr
    (output_dir / log).write_text(output, encoding="utf-8")
    audits, names_match, axioms_allowed = audit_output(output, info["expected"])
    unchanged = source.read_bytes() == source_bytes
    artifact_exists = target.is_file()
    passed = bool(result.returncode == 0 and names_match and axioms_allowed
                  and unchanged and artifact_exists and not info["forbidden"])
    elapsed = round(time.monotonic() - module_started, 3)
    entry = {
        "file": source.name,
        "sha256": sha256(source_bytes),
        "source_unchanged_during_check": unchanged,
        "command": command,
        "exit_code": result.returncode,
        "audit_count": len(audits),
        "expected_audits": info["expected"],
        "audit_names_match": names_match,
        "axioms_allowed": axioms_allowed,
        "audits": audits,
        "passed": passed,
        "forbidden_proof_commands": info["forbidden"],
        "warning_count": output.count("warning:"),
        "olean": olean.as_posix(),
        "olean_sha256": sha256(target.read_bytes()) if artifact_exists else None,
        "log": log.as_posix(),
        "elapsed_seconds": elapsed,
    }
    return entry, output


def compile_modules(order, project, output_dir, sources, initial_bytes, metadata, env,
                    jobs, report):
    """Compile bounded independent jobs; publish records only on the main thread.

    A dependency is released only after its fresh build and audits have passed.
    The unified Audit has every other local module as a prerequisite, even if
    its source import list omits one. Report entries retain the original stable
    topological order regardless of compiler completion order.
    """
    positions = {module: number for number, module in enumerate(order)}
    prerequisites = {
        module: {dep for dep in metadata[module]["imports"] if dep in metadata}
        for module in order
    }
    prerequisites["Audit"] = set(order) - {"Audit"}
    dependents = {module: set() for module in order}
    for module, deps in prerequisites.items():
        for dependency in deps:
            dependents[dependency].add(module)
    ready = [positions[module] for module in order if not prerequisites[module]]
    heapq.heapify(ready)
    entries = {}
    completed = set()
    failure = None

    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as executor:
        running = {}
        while ready or running:
            while ready and len(running) < jobs and failure is None:
                position = heapq.heappop(ready)
                module = order[position]
                print("[{}/{}] START {}".format(position + 1, len(order), sources[module].name),
                      flush=True)
                future = executor.submit(compile_module, module, project, output_dir,
                                         sources, initial_bytes, metadata, env)
                running[future] = module
            if not running:
                break
            done, _ = concurrent.futures.wait(running,
                                              return_when=concurrent.futures.FIRST_COMPLETED)
            for future in sorted(done, key=lambda item: positions[running[item]]):
                module = running.pop(future)
                try:
                    entry, output = future.result()
                except (VerificationError, OSError, ValueError) as exc:
                    if failure is None:
                        failure = exc
                    continue
                entries[module] = entry
                report["files"] = [entries[name] for name in order if name in entries]
                report["recompiled_modules"] = [entry["file"] for entry in report["files"]]
                write_report(output_dir, report)
                print("[{}/{}] {} {} ({} audits, {:.1f}s)".format(
                    positions[module] + 1, len(order), "PASS" if entry["passed"] else "FAIL",
                    entry["file"], entry["audit_count"], entry["elapsed_seconds"]), flush=True)
                if not entry["passed"]:
                    if output:
                        print(output[-12000:], file=sys.stderr, flush=True)
                    if failure is None:
                        failure = VerificationError(
                            entry["file"] + ": compilation or axiom audit failed; see "
                            + str(output_dir / entry["log"]))
                    continue
                completed.add(module)
                for dependent in dependents[module]:
                    prerequisites[dependent].remove(module)
                    if not prerequisites[dependent]:
                        heapq.heappush(ready, positions[dependent])
    if failure is not None:
        raise failure
    if len(completed) != len(order):
        raise VerificationError("Dependency scheduler could not complete every local module")


def verify(project, output_dir, jobs=1):
    project = Path(project).resolve()
    output_dir = Path(output_dir).resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    (output_dir / "modules").mkdir(exist_ok=True)
    report = {
        "schema_version": 2,
        "jobs": jobs,
        "checked_at_utc": utc_now(),
        "status": "running",
        "verification_policy": "Always recompile every local module; never resume or reuse local oleans.",
        "allowed_axioms": sorted(ALLOWED_AXIOMS),
        "files": [],
        "recompiled_modules": [],
        "reused_verified_modules": [],
        "all_requested_checks_passed": False,
    }
    report.update({flag: False for flag in MILESTONES})
    expected_files = []
    started = time.monotonic()
    write_report(output_dir, report)
    try:
        if not isinstance(jobs, int) or jobs < 1:
            raise VerificationError("jobs must be a positive integer")
        if not shutil.which("lake"):
            raise VerificationError("Lake is not on PATH. Install elan and reopen your terminal.")
        if not shutil.which("git"):
            raise VerificationError("Git is not on PATH")
        # Lake supplies all paths. Ignore any unrelated ambient import path.
        env = dict(os.environ)
        env.pop("LEAN_PATH", None)
        env.pop("LEAN_SRC_PATH", None)
        config_bytes = {name: (project / name).read_bytes() for name in CONFIG_FILES}
        report["configuration_sha256"] = {name: sha256(data) for name, data in config_bytes.items()}
        toolchain = config_bytes["lean-toolchain"].decode("utf-8").strip()
        if toolchain != TOOLCHAIN_PIN:
            raise VerificationError("lean-toolchain does not match the supported pinned toolchain")
        report["lean_toolchain"] = toolchain
        revision, clean = check_dependencies(project, env)
        report.update(mathlib_revision=revision, mathlib_clean=clean)
        version = checked_output(["lake", "env", "lean", "--version"], project, env)
        expected_version = TOOLCHAIN_PIN.rsplit(":v", 1)[1]
        if not re.search(r"\bversion " + re.escape(expected_version) + r"(?:,|\)|\s|$)", version):
            raise VerificationError("lake env lean reports a different Lean version: " + version)
        report["lean_version"] = version

        sources = discover_sources(project)
        initial_bytes = {module: path.read_bytes() for module, path in sources.items()}
        metadata = {module: source_metadata(data.decode("utf-8"))
                    for module, data in initial_bytes.items()}
        order = module_order(metadata)
        expected_files = [sources[module].name for module in order]
        report["requested_modules"] = expected_files
        report["module_count"] = len(order)
        report["source_bytes"] = sum(len(data) for data in initial_bytes.values())
        report["source_lines"] = sum(len(data.splitlines()) for data in initial_bytes.values())
        for module in order:
            expected = metadata[module]["expected"]
            if len(expected) != len(set(expected)):
                raise VerificationError(module + ": duplicate #print axioms declarations")
            if metadata[module]["forbidden"]:
                raise VerificationError(module + ": forbidden proof commands: "
                                        + ", ".join(metadata[module]["forbidden"]))
        for flag, (filename, declaration) in MILESTONES.items():
            module = Path(filename).stem
            if module not in metadata or declaration not in metadata[module]["expected"]:
                raise VerificationError("Missing milestone audit: " + flag)

        print("Verifying {} modules with {} (mathlib {}).".format(
            len(order), toolchain, revision), flush=True)
        compile_modules(order, project, output_dir, sources, initial_bytes, metadata,
                        env, jobs, report)

        report["all_sources_unchanged"] = (
            set(discover_sources(project)) == set(sources)
            and all(sources[module].read_bytes() == data for module, data in initial_bytes.items()))
        report["all_oleans_unchanged"] = all(
            (project / entry["olean"]).is_file()
            and sha256((project / entry["olean"]).read_bytes()) == entry["olean_sha256"]
            for entry in report["files"])
        report["configuration_unchanged"] = all(
            (project / name).read_bytes() == data for name, data in config_bytes.items())
        check_dependencies(project, env)
        report["dependency_check_passed_at_end"] = True
    except KeyboardInterrupt:
        report["error"] = "Verification interrupted; incomplete results are not certified."
        report["interrupted"] = True
    except (VerificationError, OSError, ValueError) as exc:
        report["error"] = str(exc)
    finally:
        summarize(report, expected_files)
        report["status"] = "passed" if report["all_requested_checks_passed"] else "failed"
        report["finished_at_utc"] = utc_now()
        report["elapsed_seconds"] = round(time.monotonic() - started, 3)
        write_report(output_dir, report)
    if report["all_requested_checks_passed"]:
        print("PASS: {} modules, {} distinct audited declarations, {} warnings.".format(
            len(report["files"]), report["distinct_proved_declarations"], report["warning_count"]), flush=True)
    else:
        print("FAIL: " + report.get("error", "Final consistency or unified audit check failed"),
              file=sys.stderr, flush=True)
    print("Report: " + str(output_dir / "verification.json"), flush=True)
    return 0 if report["all_requested_checks_passed"] else 1


def positive_jobs(value):
    try:
        jobs = int(value)
    except ValueError as exc:
        raise argparse.ArgumentTypeError("jobs must be a positive integer") from exc
    if jobs < 1:
        raise argparse.ArgumentTypeError("jobs must be a positive integer")
    return jobs


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=Path("verification"),
                        help="directory for logs/report, relative to the project (default: verification)")
    parser.add_argument("--jobs", type=positive_jobs, default=1, metavar="N",
                        help="maximum independent compiler processes (default: 1)")
    args = parser.parse_args(argv)
    project = Path(__file__).resolve().parent
    output_dir = args.output_dir if args.output_dir.is_absolute() else project / args.output_dir
    return verify(project, output_dir, jobs=args.jobs)


if __name__ == "__main__":
    sys.exit(main())
