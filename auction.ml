(* auction.ml — Multi-Agent Auction Simulator
   Demonstrates: auction mechanisms, autonomous bidding strategies,
   multi-agent game theory, adaptive learning.
   Run: ocaml auction.ml *)

(* ─── Types ──────────────────────────────────────────────────────── *)

type category = Art | Tech | Collectibles | RealEstate

type item = {
  item_name : string;
  category : category;
  reserve_price : float;
  base_value : float; (* approximate market value *)
}

type strategy = Truthful | Conservative | Aggressive | Adaptive | Sniper | Budget

type bid = {
  bidder_id : int;
  amount : float;
  tick : int;
}

type agent = {
  id : int;
  name : string;
  strategy : strategy;
  mutable budget : float;
  mutable wins : int;
  mutable total_spend : float;
  mutable total_surplus : float;
  mutable auctions_entered : int;
  mutable adaptive_multiplier : float; (* for Adaptive strategy *)
}

type auction_type = English | Dutch | SealedFirstPrice | Vickrey

type auction_result = {
  auction_kind : auction_type;
  item_sold : item;
  winner : agent option;
  price_paid : float;
  all_bids : bid list;
  surplus : float;
}

let results_log : auction_result list ref = ref []

(* ─── Utilities ──────────────────────────────────────────────────── *)

let () = Random.self_init ()

let string_of_category = function
  | Art -> "Art" | Tech -> "Tech"
  | Collectibles -> "Collectibles" | RealEstate -> "Real Estate"

let string_of_strategy = function
  | Truthful -> "truthful" | Conservative -> "conservative"
  | Aggressive -> "aggressive" | Adaptive -> "adaptive"
  | Sniper -> "sniper" | Budget -> "budget"

let string_of_auction_type = function
  | English -> "English" | Dutch -> "Dutch"
  | SealedFirstPrice -> "Sealed-1st" | Vickrey -> "Vickrey"

let strategy_of_string = function
  | "truthful" -> Some Truthful | "conservative" -> Some Conservative
  | "aggressive" -> Some Aggressive | "adaptive" -> Some Adaptive
  | "sniper" -> Some Sniper | "budget" -> Some Budget
  | _ -> None

let noise lo hi = lo +. Random.float (hi -. lo)

let valuation agent item =
  (* Each agent values item differently based on base_value + personal noise *)
  let seed = float_of_int (Hashtbl.hash (agent.id, item.item_name)) in
  let factor = 0.7 +. (mod_float (seed /. 97.0) 0.6) in
  item.base_value *. factor

(* ─── Preset Data ────────────────────────────────────────────────── *)

let preset_items = [
  { item_name = "Starry Night Print"; category = Art; reserve_price = 500.0; base_value = 1200.0 };
  { item_name = "Bronze Sculpture"; category = Art; reserve_price = 300.0; base_value = 800.0 };
  { item_name = "Vintage Macintosh"; category = Tech; reserve_price = 200.0; base_value = 600.0 };
  { item_name = "Mechanical Keyboard"; category = Tech; reserve_price = 80.0; base_value = 250.0 };
  { item_name = "First Edition Book"; category = Collectibles; reserve_price = 150.0; base_value = 500.0 };
  { item_name = "Rare Coin Set"; category = Collectibles; reserve_price = 400.0; base_value = 900.0 };
  { item_name = "Baseball Card 1952"; category = Collectibles; reserve_price = 1000.0; base_value = 3000.0 };
  { item_name = "Downtown Condo"; category = RealEstate; reserve_price = 50000.0; base_value = 120000.0 };
  { item_name = "Lakeside Cabin"; category = RealEstate; reserve_price = 30000.0; base_value = 75000.0 };
  { item_name = "GPU Cluster Node"; category = Tech; reserve_price = 2000.0; base_value = 5000.0 };
]

let items : item list ref = ref preset_items

let next_id = ref 1

let make_agent name strat budget_amt =
  let a = { id = !next_id; name; strategy = strat; budget = budget_amt;
             wins = 0; total_spend = 0.0; total_surplus = 0.0;
             auctions_entered = 0; adaptive_multiplier = 0.85 } in
  incr next_id; a

let agents : agent list ref = ref []

(* ─── Bidding Logic ──────────────────────────────────────────────── *)

let compute_bid agent item ~current_price ~tick ~max_ticks =
  let v = valuation agent item in
  if v < current_price then 0.0 (* won't bid above valuation in most cases *)
  else
    let raw = match agent.strategy with
      | Truthful -> v
      | Conservative -> v *. (noise 0.70 0.80)
      | Aggressive -> v *. (noise 0.90 1.10)
      | Adaptive -> v *. agent.adaptive_multiplier
      | Sniper ->
        if tick < max_ticks * 3 / 4 then 0.0
        else v *. (noise 0.75 0.90)
      | Budget ->
        let affordable = min v agent.budget in
        affordable *. (noise 0.70 0.90)
    in
    (* Budget hard cap *)
    min raw agent.budget

(* ─── Auction Engines ────────────────────────────────────────────── *)

let run_english item participants =
  let max_ticks = 20 in
  let current_price = ref item.reserve_price in
  let all_bids = ref [] in
  let active = Array.make (List.length participants) true in
  let parr = Array.of_list participants in
  let last_bidder = ref (-1) in
  let consecutive_passes = ref 0 in
  for tick = 1 to max_ticks do
    if !consecutive_passes < Array.length parr then begin
      let pass_count = ref 0 in
      Array.iteri (fun i ag ->
        if active.(i) then begin
          let b = compute_bid ag item ~current_price:!current_price ~tick ~max_ticks in
          if b > !current_price *. 1.05 then begin
            let amt = !current_price *. (noise 1.05 1.15) in
            let amt = min amt b in
            current_price := amt;
            all_bids := { bidder_id = ag.id; amount = amt; tick } :: !all_bids;
            last_bidder := i;
            consecutive_passes := 0
          end else begin
            incr pass_count;
            if !pass_count > 2 then active.(i) <- false
          end
        end
      ) parr;
      consecutive_passes := !pass_count
    end
  done;
  if !last_bidder >= 0 then
    let winner = parr.(!last_bidder) in
    let price = !current_price in
    let surplus = (valuation winner item) -. price in
    winner.wins <- winner.wins + 1;
    winner.total_spend <- winner.total_spend +. price;
    winner.total_surplus <- winner.total_surplus +. surplus;
    winner.budget <- winner.budget -. price;
    { auction_kind = English; item_sold = item; winner = Some winner;
      price_paid = price; all_bids = List.rev !all_bids; surplus }
  else
    { auction_kind = English; item_sold = item; winner = None;
      price_paid = 0.0; all_bids = List.rev !all_bids; surplus = 0.0 }

let run_dutch item participants =
  let start_price = item.base_value *. 2.0 in
  let max_ticks = 30 in
  let all_bids = ref [] in
  let result = ref None in
  let tick = ref 0 in
  while !result = None && !tick < max_ticks do
    incr tick;
    let price = start_price *. (0.95 ** (float_of_int !tick)) in
    if price < item.reserve_price then
      result := Some { auction_kind = Dutch; item_sold = item; winner = None;
                       price_paid = 0.0; all_bids = []; surplus = 0.0 }
    else
      List.iter (fun ag ->
        if !result = None then begin
          let v = valuation ag item in
          let accept = match ag.strategy with
            | Truthful -> price <= v
            | Conservative -> price <= v *. 0.75
            | Aggressive -> price <= v *. 1.05
            | Adaptive -> price <= v *. ag.adaptive_multiplier
            | Sniper -> price <= v *. 0.65
            | Budget -> price <= (min v ag.budget) *. 0.80
          in
          if accept then begin
            all_bids := [{ bidder_id = ag.id; amount = price; tick = !tick }];
            let surplus = v -. price in
            ag.wins <- ag.wins + 1;
            ag.total_spend <- ag.total_spend +. price;
            ag.total_surplus <- ag.total_surplus +. surplus;
            ag.budget <- ag.budget -. price;
            result := Some { auction_kind = Dutch; item_sold = item;
                             winner = Some ag; price_paid = price;
                             all_bids = !all_bids; surplus }
          end
        end
      ) participants
  done;
  match !result with
  | Some r -> r
  | None -> { auction_kind = Dutch; item_sold = item; winner = None;
              price_paid = 0.0; all_bids = []; surplus = 0.0 }

let run_sealed_bid auction_kind item participants =
  let bids = List.map (fun ag ->
    let v = valuation ag item in
    let amount = match ag.strategy with
      | Truthful -> v *. 0.95
      | Conservative -> v *. (noise 0.65 0.75)
      | Aggressive -> v *. (noise 0.90 1.05)
      | Adaptive -> v *. ag.adaptive_multiplier
      | Sniper -> v *. (noise 0.55 0.70)
      | Budget -> (min v ag.budget) *. (noise 0.70 0.85)
    in
    let amount = min amount ag.budget in
    (ag, { bidder_id = ag.id; amount; tick = 1 })
  ) participants in
  let sorted = List.sort (fun (_, b1) (_, b2) -> compare b2.amount b1.amount) bids in
  match sorted with
  | [] -> { auction_kind; item_sold = item; winner = None;
            price_paid = 0.0; all_bids = List.map snd bids; surplus = 0.0 }
  | (winner, top_bid) :: rest ->
    let price = match auction_kind with
      | Vickrey -> (match rest with (_, b2) :: _ -> b2.amount | [] -> top_bid.amount)
      | _ -> top_bid.amount
    in
    if price < item.reserve_price then
      { auction_kind; item_sold = item; winner = None;
        price_paid = 0.0; all_bids = List.map snd bids; surplus = 0.0 }
    else begin
      let surplus = (valuation winner item) -. price in
      winner.wins <- winner.wins + 1;
      winner.total_spend <- winner.total_spend +. price;
      winner.total_surplus <- winner.total_surplus +. surplus;
      winner.budget <- winner.budget -. price;
      { auction_kind; item_sold = item; winner = Some winner;
        price_paid = price; all_bids = List.map snd bids; surplus }
    end

let run_auction kind item participants =
  List.iter (fun a -> a.auctions_entered <- a.auctions_entered + 1) participants;
  let r = match kind with
    | English -> run_english item participants
    | Dutch -> run_dutch item participants
    | SealedFirstPrice -> run_sealed_bid SealedFirstPrice item participants
    | Vickrey -> run_sealed_bid Vickrey item participants
  in
  (* Update adaptive agents *)
  List.iter (fun ag ->
    if ag.strategy = Adaptive then begin
      let alpha = 0.2 in
      let target = if r.winner = Some ag then 0.80 else 0.90 in
      ag.adaptive_multiplier <- ag.adaptive_multiplier *. (1.0 -. alpha) +. target *. alpha
    end
  ) participants;
  results_log := r :: !results_log;
  r

(* ─── Display ────────────────────────────────────────────────────── *)

let print_result r =
  Printf.printf "  [%s] %s → " (string_of_auction_type r.auction_kind) r.item_sold.item_name;
  match r.winner with
  | None -> Printf.printf "NO SALE (reserve not met)\n"
  | Some w ->
    Printf.printf "Winner: %s | Paid: $%.2f | Surplus: $%.2f\n" w.name r.price_paid r.surplus

let print_agents () =
  Printf.printf "\n  %-4s %-14s %-12s %10s %5s %10s %10s\n"
    "ID" "Name" "Strategy" "Budget" "Wins" "Spend" "Surplus";
  Printf.printf "  %s\n" (String.make 70 '-');
  List.iter (fun a ->
    Printf.printf "  %-4d %-14s %-12s %10.2f %5d %10.2f %10.2f\n"
      a.id a.name (string_of_strategy a.strategy) a.budget a.wins a.total_spend a.total_surplus
  ) !agents;
  print_newline ()

let print_items () =
  Printf.printf "\n  %-22s %-14s %10s %10s\n" "Name" "Category" "Reserve" "~Value";
  Printf.printf "  %s\n" (String.make 60 '-');
  List.iter (fun i ->
    Printf.printf "  %-22s %-14s %10.2f %10.2f\n"
      i.item_name (string_of_category i.category) i.reserve_price i.base_value
  ) !items;
  print_newline ()

let print_history () =
  Printf.printf "\n  Auction History (%d auctions):\n" (List.length !results_log);
  List.iter print_result (List.rev !results_log);
  print_newline ()

let print_compare () =
  Printf.printf "\n  Strategy Comparison:\n";
  Printf.printf "  %-12s %5s %8s %10s %8s\n" "Strategy" "Wins" "Entered" "Surplus" "ROI";
  Printf.printf "  %s\n" (String.make 50 '-');
  let strategies = [Truthful; Conservative; Aggressive; Adaptive; Sniper; Budget] in
  List.iter (fun s ->
    let group = List.filter (fun a -> a.strategy = s) !agents in
    let wins = List.fold_left (fun acc a -> acc + a.wins) 0 group in
    let entered = List.fold_left (fun acc a -> acc + a.auctions_entered) 0 group in
    let surplus = List.fold_left (fun acc a -> acc +. a.total_surplus) 0.0 group in
    let spend = List.fold_left (fun acc a -> acc +. a.total_spend) 0.0 group in
    let roi = if spend > 0.0 then surplus /. spend *. 100.0 else 0.0 in
    if List.length group > 0 then
      Printf.printf "  %-12s %5d %8d %10.2f %7.1f%%\n"
        (string_of_strategy s) wins entered surplus roi
  ) strategies;
  print_newline ()

let print_chart () =
  Printf.printf "\n  Bid History (last 20 auctions, price paid):\n";
  let recent = let rec take n = function
    | [] -> [] | _ when n = 0 -> []
    | x :: xs -> x :: take (n - 1) xs
  in take 20 (List.rev !results_log) in
  let max_price = List.fold_left (fun acc r -> max acc r.price_paid) 1.0 recent in
  List.iter (fun r ->
    let bar_len = int_of_float (r.price_paid /. max_price *. 40.0) in
    let bar = String.make (max 1 bar_len) '#' in
    Printf.printf "  %-18s |%s $%.0f\n"
      (String.sub (r.item_sold.item_name ^ String.make 18 ' ') 0 18)
      bar r.price_paid
  ) recent;
  print_newline ()

(* ─── Tournament ─────────────────────────────────────────────────── *)

let run_tournament rounds =
  Printf.printf "\n  Running tournament: %d rounds x 4 auction types...\n" rounds;
  let kinds = [English; Dutch; SealedFirstPrice; Vickrey] in
  for _ = 1 to rounds do
    let item = List.nth !items (Random.int (List.length !items)) in
    List.iter (fun kind ->
      let r = run_auction kind item !agents in
      print_result r
    ) kinds
  done;
  Printf.printf "  Tournament complete! Use 'compare' to see results.\n\n"

(* ─── Demo ───────────────────────────────────────────────────────── *)

let run_demo () =
  agents := [
    make_agent "Alice" Truthful 10000.0;
    make_agent "Bob" Conservative 8000.0;
    make_agent "Charlie" Aggressive 12000.0;
    make_agent "Diana" Adaptive 9000.0;
    make_agent "Eve" Sniper 7000.0;
    make_agent "Frank" Budget 5000.0;
  ];
  items := preset_items;
  Printf.printf "\n  Demo: 6 agents, 10 items, running tournament...\n";
  run_tournament 3;
  print_compare ()

(* ─── REPL ───────────────────────────────────────────────────────── *)

let help () =
  Printf.printf "\n  Multi-Agent Auction Simulator - Commands:\n";
  Printf.printf "  %-30s %s\n" "help" "Show this help";
  Printf.printf "  %-30s %s\n" "agents" "List all agents with stats";
  Printf.printf "  %-30s %s\n" "add <name> <strategy> <budget>" "Add agent (strategies: truthful,conservative,aggressive,adaptive,sniper,budget)";
  Printf.printf "  %-30s %s\n" "items" "List available items";
  Printf.printf "  %-30s %s\n" "add_item <name> <reserve> <value>" "Add an item";
  Printf.printf "  %-30s %s\n" "english [n]" "Run English auction (item index, default random)";
  Printf.printf "  %-30s %s\n" "dutch [n]" "Run Dutch auction";
  Printf.printf "  %-30s %s\n" "sealed [n]" "Run Sealed-bid first-price auction";
  Printf.printf "  %-30s %s\n" "vickrey [n]" "Run Vickrey (second-price) auction";
  Printf.printf "  %-30s %s\n" "tournament <rounds>" "Run full tournament (all types x rounds)";
  Printf.printf "  %-30s %s\n" "compare" "Strategy comparison report";
  Printf.printf "  %-30s %s\n" "history" "Show auction log";
  Printf.printf "  %-30s %s\n" "chart" "ASCII bid chart";
  Printf.printf "  %-30s %s\n" "reset" "Reset all agents and market";
  Printf.printf "  %-30s %s\n" "demo" "Run preset demo";
  Printf.printf "  %-30s %s\n" "quit" "Exit";
  print_newline ()

let pick_item args =
  match args with
  | [n] -> (try List.nth !items (int_of_string n) with _ -> List.nth !items (Random.int (List.length !items)))
  | _ -> List.nth !items (Random.int (List.length !items))

let run_single_auction kind args =
  if !agents = [] then Printf.printf "  No agents! Use 'add' or 'demo' first.\n"
  else begin
    let item = pick_item args in
    let r = run_auction kind item !agents in
    print_result r
  end

let repl () =
  Printf.printf "\n  ╔══════════════════════════════════════════╗\n";
  Printf.printf "  ║   Multi-Agent Auction Simulator v1.0     ║\n";
  Printf.printf "  ║   Type 'help' for commands, 'demo' to    ║\n";
  Printf.printf "  ║   see it in action.                      ║\n";
  Printf.printf "  ╚══════════════════════════════════════════╝\n\n";
  let running = ref true in
  while !running do
    Printf.printf "auction> ";
    flush stdout;
    let line = try input_line stdin with End_of_file -> "quit" in
    let parts = String.split_on_char ' ' (String.trim line) in
    match parts with
    | ["quit"] | ["exit"] | ["q"] -> running := false
    | ["help"] | ["h"] | ["?"] -> help ()
    | ["agents"] -> print_agents ()
    | ["items"] -> print_items ()
    | ["history"] -> print_history ()
    | ["compare"] -> print_compare ()
    | ["chart"] -> print_chart ()
    | ["reset"] ->
      agents := []; results_log := []; items := preset_items; next_id := 1;
      Printf.printf "  Market reset.\n"
    | ["demo"] -> run_demo ()
    | "add" :: name :: strat_s :: budget_s :: _ ->
      (match strategy_of_string strat_s with
       | Some strat ->
         let b = (try float_of_string budget_s with _ -> 5000.0) in
         agents := !agents @ [make_agent name strat b];
         Printf.printf "  Added %s (%s, $%.0f)\n" name strat_s b
       | None -> Printf.printf "  Unknown strategy: %s\n" strat_s)
    | "add_item" :: name :: reserve_s :: value_s :: _ ->
      let r = (try float_of_string reserve_s with _ -> 100.0) in
      let v = (try float_of_string value_s with _ -> 500.0) in
      items := !items @ [{ item_name = name; category = Collectibles; reserve_price = r; base_value = v }];
      Printf.printf "  Added item: %s (reserve $%.0f, value ~$%.0f)\n" name r v
    | "english" :: rest -> run_single_auction English rest
    | "dutch" :: rest -> run_single_auction Dutch rest
    | "sealed" :: rest -> run_single_auction SealedFirstPrice rest
    | "vickrey" :: rest -> run_single_auction Vickrey rest
    | "tournament" :: n :: _ ->
      let rounds = (try int_of_string n with _ -> 5) in
      run_tournament rounds
    | ["tournament"] -> run_tournament 5
    | [""] | [] -> ()
    | _ -> Printf.printf "  Unknown command. Type 'help' for usage.\n"
  done;
  Printf.printf "  Goodbye!\n"

let () = repl ()
