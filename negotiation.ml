(* negotiation.ml — Automated Negotiation Protocol Simulator
   Multi-agent bilateral negotiation with strategy modeling.

   Strategies:
   - Boulware      (concedes slowly, tough early)
   - Conceder      (concedes quickly, generous early)
   - Linear        (constant concession rate)
   - Tit-for-Tat   (mirrors opponent's last concession)
   - Zeuthen       (risk-based concession — who has more to lose concedes)
   - Random Walk   (stochastic offers)

   Protocols:
   - Alternating Offers (Rubinstein)
   - Monotonic Concession Protocol

   Features:
   - Configurable deadlines & discount factors
   - Utility functions (linear, triangular, custom)
   - Nash bargaining solution computation
   - Multi-round tournament across strategy pairings
   - Autonomous deal advisor with Pareto analysis
   - Interactive REPL

   Usage: ocaml negotiation.ml
*)

(* ── Random ───────────────────────────────────────────────────────── *)

let () = Random.self_init ()
let rand_float () = Random.float 1.0

(* ── Utility functions ────────────────────────────────────────────── *)

type utility_fn =
  | Linear of float * float    (* min_val, max_val — utility = (x - min) / (max - min) *)
  | Triangular of float * float * float  (* min, peak, max *)
  | Custom of (float -> float)

let eval_utility uf x =
  match uf with
  | Linear (lo, hi) ->
    if hi <= lo then 0.0
    else Float.max 0.0 (Float.min 1.0 ((x -. lo) /. (hi -. lo)))
  | Triangular (lo, peak, hi) ->
    if x <= lo || x >= hi then 0.0
    else if x <= peak then (x -. lo) /. (peak -. lo)
    else (hi -. x) /. (hi -. peak)
  | Custom f -> Float.max 0.0 (Float.min 1.0 (f x))

(* ── Negotiation domain ───────────────────────────────────────────── *)

type issue = {
  name : string;
  lo   : float;
  hi   : float;
}

type domain = {
  issues : issue list;
}

(* An offer is a float list (one value per issue) *)
type offer = float list

let random_offer domain =
  List.map (fun iss -> iss.lo +. rand_float () *. (iss.hi -. iss.lo)) domain.issues

(* ── Agent ────────────────────────────────────────────────────────── *)

type strategy =
  | Boulware
  | Conceder
  | LinearStrat
  | TitForTat
  | Zeuthen
  | RandomWalk

let strategy_name = function
  | Boulware    -> "Boulware"
  | Conceder    -> "Conceder"
  | LinearStrat -> "Linear"
  | TitForTat   -> "Tit-for-Tat"
  | Zeuthen     -> "Zeuthen"
  | RandomWalk  -> "Random Walk"

let all_strategies = [ Boulware; Conceder; LinearStrat; TitForTat; Zeuthen; RandomWalk ]

type agent = {
  name         : string;
  strategy     : strategy;
  utility      : offer -> float;   (* utility function over offers *)
  reservation  : float;            (* minimum acceptable utility *)
  deadline     : int;              (* max rounds *)
  discount     : float;            (* per-round discount factor 0..1 *)
}

(* ── Target utility at time t ─────────────────────────────────────── *)

(* How much utility the agent demands at round t of max_t *)
let target_utility strat t max_t =
  let ratio = if max_t <= 1 then 1.0 else float_of_int t /. float_of_int (max_t - 1) in
  let ratio = Float.min 1.0 (Float.max 0.0 ratio) in
  match strat with
  | Boulware ->
    (* beta > 1 → slow concession *)
    let beta = 3.0 in
    1.0 -. (ratio ** beta)
  | Conceder ->
    (* beta < 1 → fast concession *)
    let beta = 0.33 in
    1.0 -. (ratio ** beta)
  | LinearStrat ->
    1.0 -. ratio
  | TitForTat ->
    (* starts at 0.9, will be adjusted dynamically *)
    1.0 -. ratio *. 0.6
  | Zeuthen ->
    (* placeholder; Zeuthen logic is in the protocol *)
    1.0 -. ratio *. 0.5
  | RandomWalk ->
    let noise = (rand_float () -. 0.5) *. 0.3 in
    Float.max 0.1 (Float.min 1.0 (0.7 -. ratio *. 0.4 +. noise))

(* ── Offer generation ─────────────────────────────────────────────── *)

(* Generate an offer with approximately target utility for the agent.
   Simple approach: sample several random offers, pick closest to target. *)
let generate_offer agent domain target_u =
  let best = ref (random_offer domain) in
  let best_diff = ref (Float.abs (agent.utility !best -. target_u)) in
  for _ = 1 to 200 do
    let o = random_offer domain in
    let d = Float.abs (agent.utility o -. target_u) in
    if d < !best_diff then begin
      best := o;
      best_diff := d
    end
  done;
  !best

(* ── Negotiation outcome ──────────────────────────────────────────── *)

type outcome =
  | Agreement of { offer : offer; round : int; u_a : float; u_b : float }
  | Disagreement of { reason : string; rounds : int }

(* ── Alternating Offers Protocol ──────────────────────────────────── *)

let negotiate_alternating agent_a agent_b domain =
  let max_rounds = min agent_a.deadline agent_b.deadline in
  let rec loop round last_opp_concession proposer responder =
    if round > max_rounds then
      Disagreement { reason = "deadline reached"; rounds = max_rounds }
    else begin
      let target = target_utility proposer.strategy round max_rounds in
      (* Tit-for-tat: adjust target based on opponent's concession *)
      let target =
        if proposer.strategy = TitForTat then
          match last_opp_concession with
          | None -> target
          | Some c -> Float.max proposer.reservation (target -. c *. 0.5)
        else target
      in
      let target = Float.max proposer.reservation target in
      let off = generate_offer proposer domain target in
      let u_prop = proposer.utility off in
      let u_resp = responder.utility off in
      (* Apply discount *)
      let disc = responder.discount ** float_of_int (round - 1) in
      let u_resp_disc = u_resp *. disc in
      (* Responder accepts if discounted utility ≥ reservation *)
      if u_resp_disc >= responder.reservation then begin
        let u_a, u_b =
          if proposer.name = agent_a.name then (u_prop, u_resp)
          else (u_resp, u_prop)
        in
        Agreement { offer = off; round; u_a; u_b }
      end else begin
        let concession = 1.0 -. u_prop in
        loop (round + 1) (Some concession) responder proposer
      end
    end
  in
  loop 1 None agent_a agent_b

(* ── Zeuthen protocol ─────────────────────────────────────────────── *)

(* Zeuthen risk: willingness to risk conflict *)
let zeuthen_risk utility_self offer_self offer_opp =
  let u_self = utility_self offer_self in
  let u_opp  = utility_self offer_opp in
  if u_self <= 0.001 then 1.0
  else (u_self -. u_opp) /. u_self

let negotiate_zeuthen agent_a agent_b domain =
  let max_rounds = min agent_a.deadline agent_b.deadline in
  let off_a = ref (generate_offer agent_a domain 0.95) in
  let off_b = ref (generate_offer agent_b domain 0.95) in
  let rec loop round =
    if round > max_rounds then
      Disagreement { reason = "Zeuthen deadline reached"; rounds = max_rounds }
    else begin
      let risk_a = zeuthen_risk agent_a.utility !off_a !off_b in
      let risk_b = zeuthen_risk agent_b.utility !off_b !off_a in
      (* Check acceptance *)
      if agent_a.utility !off_b >= agent_a.reservation then
        Agreement { offer = !off_b; round; u_a = agent_a.utility !off_b; u_b = agent_b.utility !off_b }
      else if agent_b.utility !off_a >= agent_b.reservation then
        Agreement { offer = !off_a; round; u_a = agent_a.utility !off_a; u_b = agent_b.utility !off_a }
      else begin
        (* Agent with lower risk concedes *)
        if risk_a <= risk_b then begin
          let target = Float.max agent_a.reservation (agent_a.utility !off_a -. 0.08) in
          off_a := generate_offer agent_a domain target
        end else begin
          let target = Float.max agent_b.reservation (agent_b.utility !off_b -. 0.08) in
          off_b := generate_offer agent_b domain target
        end;
        loop (round + 1)
      end
    end
  in
  loop 1

(* ── Nash Bargaining Solution ─────────────────────────────────────── *)

let nash_bargaining agent_a agent_b domain =
  let best = ref (random_offer domain) in
  let best_prod = ref neg_infinity in
  for _ = 1 to 5000 do
    let o = random_offer domain in
    let ua = agent_a.utility o -. agent_a.reservation in
    let ub = agent_b.utility o -. agent_b.reservation in
    if ua > 0.0 && ub > 0.0 then begin
      let prod = ua *. ub in
      if prod > !best_prod then begin
        best := o;
        best_prod := prod
      end
    end
  done;
  if !best_prod > 0.0 then
    Some (!best, agent_a.utility !best, agent_b.utility !best)
  else None

(* ── Pareto frontier (approximate) ────────────────────────────────── *)

let pareto_frontier agent_a agent_b domain n_samples =
  let samples = Array.init n_samples (fun _ ->
    let o = random_offer domain in
    (agent_a.utility o, agent_b.utility o, o)
  ) in
  (* Filter Pareto-optimal points *)
  Array.to_list samples
  |> List.filter (fun (ua, ub, _) ->
    ua >= agent_a.reservation && ub >= agent_b.reservation &&
    not (Array.exists (fun (ua2, ub2, _) ->
      ua2 > ua && ub2 > ub
    ) samples))

(* ── Autonomous Deal Advisor ──────────────────────────────────────── *)

type advice = {
  fairness_score  : float;   (* 0..1: how balanced the deal is *)
  pareto_optimal  : bool;    (* is it on the Pareto frontier? *)
  nash_distance   : float;   (* distance from Nash solution *)
  recommendation  : string;
}

let advise_deal agent_a agent_b domain outcome =
  match outcome with
  | Disagreement _ ->
    { fairness_score = 0.0; pareto_optimal = false; nash_distance = 1.0;
      recommendation = "No deal reached. Consider relaxing reservation values or extending deadlines." }
  | Agreement { offer; u_a; u_b; _ } ->
    let fairness = 1.0 -. Float.abs (u_a -. u_b) in
    let frontier = pareto_frontier agent_a agent_b domain 2000 in
    let on_frontier = List.exists (fun (fa, fb, _) ->
      Float.abs (fa -. u_a) < 0.05 && Float.abs (fb -. u_b) < 0.05
    ) frontier in
    let nash_dist = match nash_bargaining agent_a agent_b domain with
      | None -> 1.0
      | Some (_, na, nb) ->
        sqrt ((u_a -. na) ** 2.0 +. (u_b -. nb) ** 2.0)
    in
    let rec_msg =
      if fairness > 0.8 && on_frontier then
        "Excellent deal — fair and Pareto-efficient."
      else if fairness > 0.8 then
        "Fair deal but may not be Pareto-optimal. Room for joint improvement."
      else if on_frontier then
        Printf.sprintf "Efficient but imbalanced (%.0f%% fairness). %s got a better deal."
          (fairness *. 100.0) (if u_a > u_b then agent_a.name else agent_b.name)
      else
        Printf.sprintf "Sub-optimal deal. Both agents could improve. Nash distance: %.3f" nash_dist
    in
    let _ = offer in  (* suppress warning *)
    { fairness_score = fairness; pareto_optimal = on_frontier;
      nash_distance = nash_dist; recommendation = rec_msg }

(* ── Display ──────────────────────────────────────────────────────── *)

let show_offer domain offer =
  List.combine domain.issues offer
  |> List.map (fun (iss, v) -> Printf.sprintf "%s=%.2f" iss.name v)
  |> String.concat ", "

let show_outcome domain = function
  | Agreement { offer; round; u_a; u_b } ->
    Printf.printf "  ✅ Agreement at round %d\n" round;
    Printf.printf "     Offer: %s\n" (show_offer domain offer);
    Printf.printf "     Utility A: %.3f  |  Utility B: %.3f\n" u_a u_b
  | Disagreement { reason; rounds } ->
    Printf.printf "  ❌ Disagreement after %d rounds: %s\n" rounds reason

let show_advice adv =
  Printf.printf "  📊 Deal Advisor:\n";
  Printf.printf "     Fairness: %.0f%%  |  Pareto: %s  |  Nash dist: %.3f\n"
    (adv.fairness_score *. 100.0)
    (if adv.pareto_optimal then "yes" else "no")
    adv.nash_distance;
  Printf.printf "     → %s\n" adv.recommendation

(* ── Preset domains ───────────────────────────────────────────────── *)

let salary_domain = {
  issues = [
    { name = "salary"; lo = 50000.0; hi = 120000.0 };
    { name = "vacation_days"; lo = 10.0; hi = 30.0 };
    { name = "remote_pct"; lo = 0.0; hi = 100.0 };
  ]
}

let trade_domain = {
  issues = [
    { name = "price"; lo = 1.0; hi = 100.0 };
    { name = "quantity"; lo = 1.0; hi = 1000.0 };
    { name = "delivery_days"; lo = 1.0; hi = 60.0 };
  ]
}

let treaty_domain = {
  issues = [
    { name = "territory_pct"; lo = 0.0; hi = 100.0 };
    { name = "reparations"; lo = 0.0; hi = 1000000.0 };
    { name = "troop_limit"; lo = 0.0; hi = 50000.0 };
  ]
}

let domains = [
  ("salary",  salary_domain,  "Job offer negotiation (salary, vacation, remote work)");
  ("trade",   trade_domain,   "Trade deal (price, quantity, delivery)");
  ("treaty",  treaty_domain,  "Peace treaty (territory, reparations, troop limits)");
]

(* ── Agent factory ────────────────────────────────────────────────── *)

(* Simple linear utility: weighted sum of normalized issue values *)
let make_linear_utility domain weights prefer_high =
  fun (offer : offer) ->
    let parts = List.combine (List.combine domain.issues weights) (List.combine offer prefer_high) in
    List.fold_left (fun acc ((iss, w), (v, high)) ->
      let norm =
        if iss.hi <= iss.lo then 0.0
        else if high then (v -. iss.lo) /. (iss.hi -. iss.lo)
        else (iss.hi -. v) /. (iss.hi -. iss.lo)
      in
      acc +. w *. norm
    ) 0.0 parts

let make_agent name strategy domain weights prefer_high reservation deadline discount =
  { name; strategy;
    utility = make_linear_utility domain weights prefer_high;
    reservation; deadline; discount }

(* ── Preset scenarios ─────────────────────────────────────────────── *)

let salary_agents s1 s2 =
  let a = make_agent "Candidate" s1 salary_domain [0.5; 0.3; 0.2] [true; true; true] 0.3 20 0.98 in
  let b = make_agent "Employer"  s2 salary_domain [0.5; 0.3; 0.2] [false; false; false] 0.3 20 0.95 in
  (a, b, salary_domain)

let trade_agents s1 s2 =
  let a = make_agent "Seller" s1 trade_domain [0.6; 0.2; 0.2] [true; false; true] 0.25 15 0.97 in
  let b = make_agent "Buyer"  s2 trade_domain [0.6; 0.2; 0.2] [false; true; false] 0.25 15 0.96 in
  (a, b, trade_domain)

let treaty_agents s1 s2 =
  let a = make_agent "Nation-A" s1 treaty_domain [0.4; 0.3; 0.3] [true; false; true] 0.2 30 0.99 in
  let b = make_agent "Nation-B" s2 treaty_domain [0.4; 0.3; 0.3] [false; true; false] 0.2 30 0.99 in
  (a, b, treaty_domain)

(* ── Tournament ───────────────────────────────────────────────────── *)

type tournament_entry = {
  strat_a    : strategy;
  strat_b    : strategy;
  agreements : int;
  total      : int;
  avg_ua     : float;
  avg_ub     : float;
  avg_rounds : float;
}

let run_tournament domain_fn n_trials =
  let results = ref [] in
  List.iter (fun sa ->
    List.iter (fun sb ->
      let agree = ref 0 in
      let sum_ua = ref 0.0 in
      let sum_ub = ref 0.0 in
      let sum_rd = ref 0 in
      for _ = 1 to n_trials do
        let (a, b, dom) = domain_fn sa sb in
        let outcome = negotiate_alternating a b dom in
        match outcome with
        | Agreement { u_a; u_b; round; _ } ->
          incr agree;
          sum_ua := !sum_ua +. u_a;
          sum_ub := !sum_ub +. u_b;
          sum_rd := !sum_rd + round
        | Disagreement _ -> ()
      done;
      let ag = !agree in
      results := {
        strat_a = sa; strat_b = sb;
        agreements = ag; total = n_trials;
        avg_ua = if ag > 0 then !sum_ua /. float_of_int ag else 0.0;
        avg_ub = if ag > 0 then !sum_ub /. float_of_int ag else 0.0;
        avg_rounds = if ag > 0 then float_of_int !sum_rd /. float_of_int ag else 0.0;
      } :: !results
    ) all_strategies
  ) all_strategies;
  List.rev !results

let show_tournament results =
  Printf.printf "\n  %-12s vs %-12s | Agree | Avg UA | Avg UB | Avg Rnd\n" "Strategy A" "Strategy B";
  Printf.printf "  %s\n" (String.make 72 '-');
  List.iter (fun e ->
    Printf.printf "  %-12s vs %-12s | %3d%%  | %.3f  | %.3f  | %.1f\n"
      (strategy_name e.strat_a) (strategy_name e.strat_b)
      (if e.total > 0 then e.agreements * 100 / e.total else 0)
      e.avg_ua e.avg_ub e.avg_rounds
  ) results

(* ── Strategy analysis ────────────────────────────────────────────── *)

let analyze_strategies results =
  Printf.printf "\n  📈 Strategy Performance Summary:\n";
  List.iter (fun s ->
    let as_a = List.filter (fun e -> e.strat_a = s) results in
    let as_b = List.filter (fun e -> e.strat_b = s) results in
    let total_agree_a = List.fold_left (fun acc e -> acc + e.agreements) 0 as_a in
    let total_trials_a = List.fold_left (fun acc e -> acc + e.total) 0 as_a in
    let total_agree_b = List.fold_left (fun acc e -> acc + e.agreements) 0 as_b in
    let total_trials_b = List.fold_left (fun acc e -> acc + e.total) 0 as_b in
    let avg_u_a = if total_agree_a > 0 then
      List.fold_left (fun acc e -> acc +. e.avg_ua *. float_of_int e.agreements) 0.0 as_a
      /. float_of_int total_agree_a
    else 0.0 in
    let avg_u_b = if total_agree_b > 0 then
      List.fold_left (fun acc e -> acc +. e.avg_ub *. float_of_int e.agreements) 0.0 as_b
      /. float_of_int total_agree_b
    else 0.0 in
    let deal_rate = if total_trials_a + total_trials_b > 0 then
      float_of_int (total_agree_a + total_agree_b)
      /. float_of_int (total_trials_a + total_trials_b) *. 100.0
    else 0.0 in
    Printf.printf "     %-12s  deal rate: %.0f%%  avg utility (as A): %.3f  (as B): %.3f\n"
      (strategy_name s) deal_rate avg_u_a avg_u_b
  ) all_strategies;
  (* Find best overall *)
  let best = List.fold_left (fun (bs, bv) s ->
    let entries = List.filter (fun e -> e.strat_a = s || e.strat_b = s) results in
    let total_u = List.fold_left (fun acc e ->
      if e.strat_a = s then acc +. e.avg_ua *. float_of_int e.agreements
      else acc +. e.avg_ub *. float_of_int e.agreements
    ) 0.0 entries in
    let total_deals = List.fold_left (fun acc e ->
      if e.strat_a = s then acc + e.agreements
      else acc + e.agreements
    ) 0 entries in
    let avg = if total_deals > 0 then total_u /. float_of_int total_deals else 0.0 in
    if avg > bv then (s, avg) else (bs, bv)
  ) (Boulware, 0.0) all_strategies in
  Printf.printf "     🏆 Best overall: %s (avg utility: %.3f)\n" (strategy_name (fst best)) (snd best)

(* ── REPL ─────────────────────────────────────────────────────────── *)

let print_help () =
  Printf.printf "\n  Automated Negotiation Protocol Simulator\n";
  Printf.printf "  ═════════════════════════════════════════\n\n";
  Printf.printf "  Commands:\n";
  Printf.printf "    negotiate <domain> <stratA> <stratB>  Run single negotiation\n";
  Printf.printf "    zeuthen <domain> <stratA> <stratB>    Run Zeuthen protocol\n";
  Printf.printf "    nash <domain>                         Compute Nash bargaining solution\n";
  Printf.printf "    pareto <domain>                       Show Pareto frontier samples\n";
  Printf.printf "    tournament <domain> [trials]          Run all-vs-all tournament\n";
  Printf.printf "    demo                                  Run showcase demo\n";
  Printf.printf "    domains                               List available domains\n";
  Printf.printf "    strategies                            List strategies\n";
  Printf.printf "    help                                  Show this help\n";
  Printf.printf "    quit                                  Exit\n\n";
  Printf.printf "  Domains: salary, trade, treaty\n";
  Printf.printf "  Strategies: boulware, conceder, linear, tft, zeuthen, random\n\n"

let parse_strategy = function
  | "boulware" | "b"  -> Some Boulware
  | "conceder" | "c"  -> Some Conceder
  | "linear"   | "l"  -> Some LinearStrat
  | "tft" | "titfortat" | "t" -> Some TitForTat
  | "zeuthen"  | "z"  -> Some Zeuthen
  | "random"   | "r"  -> Some RandomWalk
  | _ -> None

let parse_domain = function
  | "salary" | "s"  -> Some salary_agents
  | "trade"  | "t"  -> Some trade_agents
  | "treaty" | "p"  -> Some treaty_agents
  | _ -> None

let get_domain_obj = function
  | "salary" | "s"  -> Some salary_domain
  | "trade"  | "t"  -> Some trade_domain
  | "treaty" | "p"  -> Some treaty_domain
  | _ -> None

let run_demo () =
  Printf.printf "\n  ═══ Negotiation Demo ═══\n\n";
  (* Demo 1: Salary negotiation *)
  Printf.printf "  📋 Scenario 1: Salary Negotiation (Boulware vs Conceder)\n";
  let (a, b, dom) = salary_agents Boulware Conceder in
  let outcome = negotiate_alternating a b dom in
  show_outcome dom outcome;
  let adv = advise_deal a b dom outcome in
  show_advice adv;

  Printf.printf "\n  📋 Scenario 2: Trade Deal (Tit-for-Tat vs Linear)\n";
  let (a, b, dom) = trade_agents TitForTat LinearStrat in
  let outcome = negotiate_alternating a b dom in
  show_outcome dom outcome;
  let adv = advise_deal a b dom outcome in
  show_advice adv;

  Printf.printf "\n  📋 Scenario 3: Peace Treaty via Zeuthen Protocol\n";
  let (a, b, dom) = treaty_agents Zeuthen Zeuthen in
  let outcome = negotiate_zeuthen a b dom in
  show_outcome dom outcome;
  let adv = advise_deal a b dom outcome in
  show_advice adv;

  Printf.printf "\n  📋 Scenario 4: Tournament (Salary domain, 50 trials each)\n";
  let results = run_tournament salary_agents 50 in
  show_tournament results;
  analyze_strategies results;
  Printf.printf "\n"

let () =
  print_help ();
  run_demo ();
  Printf.printf "\n";
  let running = ref true in
  while !running do
    Printf.printf "  negotiation> %!";
    let line = try Some (input_line stdin) with End_of_file -> None in
    match line with
    | None -> running := false
    | Some line ->
      let parts = String.split_on_char ' ' (String.trim line)
        |> List.filter (fun s -> s <> "") in
      match parts with
      | [] -> ()
      | ["quit"] | ["exit"] | ["q"] -> running := false
      | ["help"] | ["h"] -> print_help ()
      | ["demo"] | ["d"] -> run_demo ()
      | ["domains"] ->
        List.iter (fun (n, _, desc) -> Printf.printf "  %-10s %s\n" n desc) domains
      | ["strategies"] ->
        List.iter (fun s -> Printf.printf "  %s\n" (strategy_name s)) all_strategies
      | ["negotiate"; dom_s; sa_s; sb_s] ->
        (match parse_domain dom_s, parse_strategy sa_s, parse_strategy sb_s with
         | Some dfn, Some sa, Some sb ->
           let (a, b, dom) = dfn sa sb in
           let outcome = negotiate_alternating a b dom in
           show_outcome dom outcome;
           let adv = advise_deal a b dom outcome in
           show_advice adv
         | _ -> Printf.printf "  Unknown domain or strategy. Type 'help'.\n")
      | ["zeuthen"; dom_s; sa_s; sb_s] ->
        (match parse_domain dom_s, parse_strategy sa_s, parse_strategy sb_s with
         | Some dfn, Some sa, Some sb ->
           let (a, b, dom) = dfn sa sb in
           let outcome = negotiate_zeuthen a b dom in
           show_outcome dom outcome;
           let adv = advise_deal a b dom outcome in
           show_advice adv
         | _ -> Printf.printf "  Unknown domain or strategy. Type 'help'.\n")
      | ["nash"; dom_s] ->
        (match get_domain_obj dom_s with
         | Some dom ->
           let (a, b, _) = salary_agents Boulware Conceder in
           (match nash_bargaining a b dom with
            | Some (off, ua, ub) ->
              Printf.printf "  Nash solution: %s\n" (show_offer dom off);
              Printf.printf "  Utility A: %.3f  |  Utility B: %.3f\n" ua ub
            | None -> Printf.printf "  No feasible Nash solution found.\n")
         | None -> Printf.printf "  Unknown domain.\n")
      | ["pareto"; dom_s] ->
        (match get_domain_obj dom_s with
         | Some dom ->
           let (a, b, _) = salary_agents Boulware Conceder in
           let frontier = pareto_frontier a b dom 3000 in
           Printf.printf "  Pareto frontier (%d points):\n" (List.length frontier);
           let shown = ref 0 in
           List.iter (fun (ua, ub, off) ->
             if !shown < 10 then begin
               Printf.printf "    UA=%.3f UB=%.3f  %s\n" ua ub (show_offer dom off);
               incr shown
             end
           ) frontier;
           if List.length frontier > 10 then
             Printf.printf "    ... (%d more)\n" (List.length frontier - 10)
         | None -> Printf.printf "  Unknown domain.\n")
      | "tournament" :: dom_s :: rest ->
        let trials = match rest with
          | [n] -> (try int_of_string n with _ -> 30)
          | _ -> 30
        in
        (match parse_domain dom_s with
         | Some dfn ->
           Printf.printf "  Running tournament (%d trials per pairing)...\n" trials;
           let results = run_tournament dfn trials in
           show_tournament results;
           analyze_strategies results
         | None -> Printf.printf "  Unknown domain.\n")
      | _ -> Printf.printf "  Unknown command. Type 'help'.\n"
  done;
  Printf.printf "  Goodbye!\n"
