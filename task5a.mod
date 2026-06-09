set VENUES;
set SPORTS;
set WEEKS;

param venue_order {VENUES} >= 0;

set PAIRS := {j in VENUES, k in VENUES: venue_order[j] < venue_order[k]};
set TRIPLES := {j in VENUES, k in VENUES, l in VENUES:
                    venue_order[j] < venue_order[k] and venue_order[k] < venue_order[l]};

param cost       {VENUES} >= 0;
param capacity   {VENUES} >= 0;
param max_sports {VENUES} >= 0;
param eligible   {SPORTS, VENUES} >= 0;
param sessions   {SPORTS} >= 0;
param demand     {SPORTS} >= 0;

param ticket_value := 5;
param bus_cost     := 20;

param tps {i in SPORTS, j in VENUES} :=
    if demand[i] <= capacity[j] then demand[i] else capacity[j];

# Big-M per venue: max possible attendance from any eligible sport
param Mv {j in VENUES} := max {i in SPORTS} tps[i,j];

var y {VENUES} binary;
var x {SPORTS, VENUES, WEEKS} binary;
var w {SPORTS, WEEKS} binary;
var s {SPORTS, VENUES, WEEKS} >= 0;

var bus2  {(j,k) in PAIRS}     binary;
var bus3  {(j,k,l) in TRIPLES} binary;
var active {VENUES, WEEKS}     binary;

var z2    {(j,k) in PAIRS,     t in WEEKS} binary;
var z3jk  {(j,k,l) in TRIPLES, t in WEEKS} binary;
var z3jl  {(j,k,l) in TRIPLES, t in WEEKS} binary;
var z3kl  {(j,k,l) in TRIPLES, t in WEEKS} binary;
var z3all {(j,k,l) in TRIPLES, t in WEEKS} binary;

# Attendance at venue j during week t
var attend {VENUES, WEEKS} >= 0;

# Per-pair: attend gated by z2
var u2j {(j,k) in PAIRS, t in WEEKS} >= 0;
var u2k {(j,k) in PAIRS, t in WEEKS} >= 0;

# Per-triple: attend gated by each z3 indicator
var u3jk_j {(j,k,l) in TRIPLES, t in WEEKS} >= 0;
var u3jk_k {(j,k,l) in TRIPLES, t in WEEKS} >= 0;
var u3jl_j {(j,k,l) in TRIPLES, t in WEEKS} >= 0;
var u3jl_l {(j,k,l) in TRIPLES, t in WEEKS} >= 0;
var u3kl_k {(j,k,l) in TRIPLES, t in WEEKS} >= 0;
var u3kl_l {(j,k,l) in TRIPLES, t in WEEKS} >= 0;
var u3all_j {(j,k,l) in TRIPLES, t in WEEKS} >= 0;
var u3all_k {(j,k,l) in TRIPLES, t in WEEKS} >= 0;
var u3all_l {(j,k,l) in TRIPLES, t in WEEKS} >= 0;

minimize Total_Cost:
  (sum {j in VENUES} cost[j] * y[j])
  + bus_cost * (sum {(j,k) in PAIRS}     bus2[j,k]
              + sum {(j,k,l) in TRIPLES} bus3[j,k,l])
  - ticket_value * (sum {i in SPORTS, j in VENUES, t in WEEKS} s[i,j,t])
  - ticket_value * 0.10 * (sum {(j,k) in PAIRS, t in WEEKS} (u2j[j,k,t] + u2k[j,k,t]))
  - ticket_value * (sum {(j,k,l) in TRIPLES, t in WEEKS} (
        0.10 * (u3jk_j[j,k,l,t] + u3jk_k[j,k,l,t])
      + 0.10 * (u3jl_j[j,k,l,t] + u3jl_l[j,k,l,t])
      + 0.10 * (u3kl_k[j,k,l,t] + u3kl_l[j,k,l,t])
      - 0.06 * (u3all_j[j,k,l,t] + u3all_k[j,k,l,t] + u3all_l[j,k,l,t])
    ));

subject to

# Define attendance: equals scheduled sport's tps, or 0
attend_def {j in VENUES, t in WEEKS}:
    attend[j,t] = sum {i in SPORTS} tps[i,j] * x[i,j,t];

active_eq {j in VENUES, t in WEEKS}:
    active[j,t] = sum {i in SPORTS} x[i,j,t];

one_network {j in VENUES}:
    (sum {(j2,k) in PAIRS:     j2 = j or k = j}          bus2[j2,k])
  + (sum {(j2,k,l) in TRIPLES: j2 = j or k = j or l = j} bus3[j2,k,l]) <= 1;

z2_ub1 {(j,k) in PAIRS, t in WEEKS}: z2[j,k,t] <= bus2[j,k];
z2_ub2 {(j,k) in PAIRS, t in WEEKS}: z2[j,k,t] <= active[j,t];
z2_ub3 {(j,k) in PAIRS, t in WEEKS}: z2[j,k,t] <= active[k,t];
z2_lb  {(j,k) in PAIRS, t in WEEKS}: z2[j,k,t] >= bus2[j,k] + active[j,t] + active[k,t] - 2;

z3jk_ub1 {(j,k,l) in TRIPLES, t in WEEKS}: z3jk[j,k,l,t] <= bus3[j,k,l];
z3jk_ub2 {(j,k,l) in TRIPLES, t in WEEKS}: z3jk[j,k,l,t] <= active[j,t];
z3jk_ub3 {(j,k,l) in TRIPLES, t in WEEKS}: z3jk[j,k,l,t] <= active[k,t];
z3jk_lb  {(j,k,l) in TRIPLES, t in WEEKS}: z3jk[j,k,l,t] >= bus3[j,k,l] + active[j,t] + active[k,t] - 2;

z3jl_ub1 {(j,k,l) in TRIPLES, t in WEEKS}: z3jl[j,k,l,t] <= bus3[j,k,l];
z3jl_ub2 {(j,k,l) in TRIPLES, t in WEEKS}: z3jl[j,k,l,t] <= active[j,t];
z3jl_ub3 {(j,k,l) in TRIPLES, t in WEEKS}: z3jl[j,k,l,t] <= active[l,t];
z3jl_lb  {(j,k,l) in TRIPLES, t in WEEKS}: z3jl[j,k,l,t] >= bus3[j,k,l] + active[j,t] + active[l,t] - 2;

z3kl_ub1 {(j,k,l) in TRIPLES, t in WEEKS}: z3kl[j,k,l,t] <= bus3[j,k,l];
z3kl_ub2 {(j,k,l) in TRIPLES, t in WEEKS}: z3kl[j,k,l,t] <= active[k,t];
z3kl_ub3 {(j,k,l) in TRIPLES, t in WEEKS}: z3kl[j,k,l,t] <= active[l,t];
z3kl_lb  {(j,k,l) in TRIPLES, t in WEEKS}: z3kl[j,k,l,t] >= bus3[j,k,l] + active[k,t] + active[l,t] - 2;

z3all_ub1 {(j,k,l) in TRIPLES, t in WEEKS}: z3all[j,k,l,t] <= bus3[j,k,l];
z3all_ub2 {(j,k,l) in TRIPLES, t in WEEKS}: z3all[j,k,l,t] <= active[j,t];
z3all_ub3 {(j,k,l) in TRIPLES, t in WEEKS}: z3all[j,k,l,t] <= active[k,t];
z3all_ub4 {(j,k,l) in TRIPLES, t in WEEKS}: z3all[j,k,l,t] <= active[l,t];
z3all_lb  {(j,k,l) in TRIPLES, t in WEEKS}: z3all[j,k,l,t] >= bus3[j,k,l]
    + active[j,t] + active[k,t] + active[l,t] - 3;

# Big-M linearization: u = attend when z = 1, else 0
u2j_ub1 {(j,k) in PAIRS, t in WEEKS}: u2j[j,k,t] <= attend[j,t];
u2j_ub2 {(j,k) in PAIRS, t in WEEKS}: u2j[j,k,t] <= Mv[j] * z2[j,k,t];
u2j_lb  {(j,k) in PAIRS, t in WEEKS}: u2j[j,k,t] >= attend[j,t] - Mv[j] * (1 - z2[j,k,t]);

u2k_ub1 {(j,k) in PAIRS, t in WEEKS}: u2k[j,k,t] <= attend[k,t];
u2k_ub2 {(j,k) in PAIRS, t in WEEKS}: u2k[j,k,t] <= Mv[k] * z2[j,k,t];
u2k_lb  {(j,k) in PAIRS, t in WEEKS}: u2k[j,k,t] >= attend[k,t] - Mv[k] * (1 - z2[j,k,t]);

u3jk_j_ub1 {(j,k,l) in TRIPLES, t in WEEKS}: u3jk_j[j,k,l,t] <= attend[j,t];
u3jk_j_ub2 {(j,k,l) in TRIPLES, t in WEEKS}: u3jk_j[j,k,l,t] <= Mv[j] * z3jk[j,k,l,t];
u3jk_j_lb  {(j,k,l) in TRIPLES, t in WEEKS}: u3jk_j[j,k,l,t] >= attend[j,t] - Mv[j] * (1 - z3jk[j,k,l,t]);

u3jk_k_ub1 {(j,k,l) in TRIPLES, t in WEEKS}: u3jk_k[j,k,l,t] <= attend[k,t];
u3jk_k_ub2 {(j,k,l) in TRIPLES, t in WEEKS}: u3jk_k[j,k,l,t] <= Mv[k] * z3jk[j,k,l,t];
u3jk_k_lb  {(j,k,l) in TRIPLES, t in WEEKS}: u3jk_k[j,k,l,t] >= attend[k,t] - Mv[k] * (1 - z3jk[j,k,l,t]);

u3jl_j_ub1 {(j,k,l) in TRIPLES, t in WEEKS}: u3jl_j[j,k,l,t] <= attend[j,t];
u3jl_j_ub2 {(j,k,l) in TRIPLES, t in WEEKS}: u3jl_j[j,k,l,t] <= Mv[j] * z3jl[j,k,l,t];
u3jl_j_lb  {(j,k,l) in TRIPLES, t in WEEKS}: u3jl_j[j,k,l,t] >= attend[j,t] - Mv[j] * (1 - z3jl[j,k,l,t]);

u3jl_l_ub1 {(j,k,l) in TRIPLES, t in WEEKS}: u3jl_l[j,k,l,t] <= attend[l,t];
u3jl_l_ub2 {(j,k,l) in TRIPLES, t in WEEKS}: u3jl_l[j,k,l,t] <= Mv[l] * z3jl[j,k,l,t];
u3jl_l_lb  {(j,k,l) in TRIPLES, t in WEEKS}: u3jl_l[j,k,l,t] >= attend[l,t] - Mv[l] * (1 - z3jl[j,k,l,t]);

u3kl_k_ub1 {(j,k,l) in TRIPLES, t in WEEKS}: u3kl_k[j,k,l,t] <= attend[k,t];
u3kl_k_ub2 {(j,k,l) in TRIPLES, t in WEEKS}: u3kl_k[j,k,l,t] <= Mv[k] * z3kl[j,k,l,t];
u3kl_k_lb  {(j,k,l) in TRIPLES, t in WEEKS}: u3kl_k[j,k,l,t] >= attend[k,t] - Mv[k] * (1 - z3kl[j,k,l,t]);

u3kl_l_ub1 {(j,k,l) in TRIPLES, t in WEEKS}: u3kl_l[j,k,l,t] <= attend[l,t];
u3kl_l_ub2 {(j,k,l) in TRIPLES, t in WEEKS}: u3kl_l[j,k,l,t] <= Mv[l] * z3kl[j,k,l,t];
u3kl_l_lb  {(j,k,l) in TRIPLES, t in WEEKS}: u3kl_l[j,k,l,t] >= attend[l,t] - Mv[l] * (1 - z3kl[j,k,l,t]);

u3all_j_ub1 {(j,k,l) in TRIPLES, t in WEEKS}: u3all_j[j,k,l,t] <= attend[j,t];
u3all_j_ub2 {(j,k,l) in TRIPLES, t in WEEKS}: u3all_j[j,k,l,t] <= Mv[j] * z3all[j,k,l,t];
u3all_j_lb  {(j,k,l) in TRIPLES, t in WEEKS}: u3all_j[j,k,l,t] >= attend[j,t] - Mv[j] * (1 - z3all[j,k,l,t]);

u3all_k_ub1 {(j,k,l) in TRIPLES, t in WEEKS}: u3all_k[j,k,l,t] <= attend[k,t];
u3all_k_ub2 {(j,k,l) in TRIPLES, t in WEEKS}: u3all_k[j,k,l,t] <= Mv[k] * z3all[j,k,l,t];
u3all_k_lb  {(j,k,l) in TRIPLES, t in WEEKS}: u3all_k[j,k,l,t] >= attend[k,t] - Mv[k] * (1 - z3all[j,k,l,t]);

u3all_l_ub1 {(j,k,l) in TRIPLES, t in WEEKS}: u3all_l[j,k,l,t] <= attend[l,t];
u3all_l_ub2 {(j,k,l) in TRIPLES, t in WEEKS}: u3all_l[j,k,l,t] <= Mv[l] * z3all[j,k,l,t];
u3all_l_lb  {(j,k,l) in TRIPLES, t in WEEKS}: u3all_l[j,k,l,t] >= attend[l,t] - Mv[l] * (1 - z3all[j,k,l,t]);

# Bus networks can only use opened venues
bus2_open_j {(j,k) in PAIRS}: bus2[j,k] <= y[j];
bus2_open_k {(j,k) in PAIRS}: bus2[j,k] <= y[k];

bus3_open_j {(j,k,l) in TRIPLES}: bus3[j,k,l] <= y[j];
bus3_open_k {(j,k,l) in TRIPLES}: bus3[j,k,l] <= y[k];
bus3_open_l {(j,k,l) in TRIPLES}: bus3[j,k,l] <= y[l];

# z indicators can't fire if the bus isn't built or the venue isn't active
# (tighter versions of the existing z2_lb)
z2_open_j {(j,k) in PAIRS, t in WEEKS}: z2[j,k,t] <= y[j];
z2_open_k {(j,k) in PAIRS, t in WEEKS}: z2[j,k,t] <= y[k];

# u variables capped by the actual attendance bound (tighter than Mv when y=0)
u2j_y {(j,k) in PAIRS, t in WEEKS}: u2j[j,k,t] <= Mv[j] * y[j];
u2k_y {(j,k) in PAIRS, t in WEEKS}: u2k[j,k,t] <= Mv[k] * y[k];

u3jk_j_y {(j,k,l) in TRIPLES, t in WEEKS}: u3jk_j[j,k,l,t] <= Mv[j] * y[j];
u3jk_k_y {(j,k,l) in TRIPLES, t in WEEKS}: u3jk_k[j,k,l,t] <= Mv[k] * y[k];
u3jl_j_y {(j,k,l) in TRIPLES, t in WEEKS}: u3jl_j[j,k,l,t] <= Mv[j] * y[j];
u3jl_l_y {(j,k,l) in TRIPLES, t in WEEKS}: u3jl_l[j,k,l,t] <= Mv[l] * y[l];
u3kl_k_y {(j,k,l) in TRIPLES, t in WEEKS}: u3kl_k[j,k,l,t] <= Mv[k] * y[k];
u3kl_l_y {(j,k,l) in TRIPLES, t in WEEKS}: u3kl_l[j,k,l,t] <= Mv[l] * y[l];
u3all_j_y {(j,k,l) in TRIPLES, t in WEEKS}: u3all_j[j,k,l,t] <= Mv[j] * y[j];
u3all_k_y {(j,k,l) in TRIPLES, t in WEEKS}: u3all_k[j,k,l,t] <= Mv[k] * y[k];
u3all_l_y {(j,k,l) in TRIPLES, t in WEEKS}: u3all_l[j,k,l,t] <= Mv[l] * y[l];


# Original Task 2/3 constraints
one_week {i in SPORTS}: sum {t in WEEKS} w[i,t] = 1;

sessions_constraint {i in SPORTS, t in WEEKS}:
    sum {j in VENUES} x[i,j,t] = sessions[i] * w[i,t];

eligibility {i in SPORTS, j in VENUES, t in WEEKS}:
    x[i,j,t] <= eligible[i,j] * y[j];

max_sports_limit {j in VENUES}:
    sum {i in SPORTS, t in WEEKS} x[i,j,t] <= max_sports[j] * y[j];

one_sport_per_week {j in VENUES, t in WEEKS}:
    sum {i in SPORTS} x[i,j,t] <= 1;

week_availability {i in SPORTS, j in VENUES, t in WEEKS: t > max_sports[j]}:
    x[i,j,t] = 0;

ticket_demand {i in SPORTS, j in VENUES, t in WEEKS}:
    s[i,j,t] <= demand[i] * x[i,j,t];

ticket_capacity {i in SPORTS, j in VENUES, t in WEEKS}:
    s[i,j,t] <= capacity[j] * x[i,j,t];