import CRGPolynomialExponentialOrder
import Lean

open Lean Elab Command

def proofClosure (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    if let some info := env.find? name then
      for dep in info.getUsedConstantsAsSet.toList do
        if !seen.contains dep then todo := todo.push dep
  return seen

run_cmd do
  let env ← getEnv
  let roots : Array Name := #[
    `CRGPolynomialExponentialOrder.polynomial_exponential_order_one,
    `CRGConstantMultiplierOrder.order_one_of_constant_multipliers,
    `CRGLinearPhaseEndgame.order_one_of_linear_phases]
  for root in roots do
    if (env.find? root).isNone then throwError "Missing endpoint: {root}"
  let rows := roots.map fun root =>
    let deps := proofClosure env root
    let localDeps := deps.toList.filter fun n =>
      ["LiWangWen.", "WimanValiron.", "Helmrath", "IncePeriodic.", "WasowConstant", "CRGConstant", "CRGLinearPhase", "CRGFixedGauge", "CRGOrderPhase"].any
        (fun pre => pre.isPrefixOf n.toString)
    Json.mkObj [("declaration", toJson root.toString),
      ("dependency_count", toJson deps.size),
      ("local_dependencies", toJson (localDeps.map Name.toString).mergeSort)]
  logInfo m!"ROUTE_AUDIT_JSON:{(Json.arr rows).compress}"
