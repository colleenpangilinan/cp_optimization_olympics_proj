set VENUES;
set SPORTS;
set WEEKS;

param cost        {VENUES};
param capacity    {VENUES};
param max_sports  {VENUES};
param eligible    {SPORTS, VENUES};
param sessions    {SPORTS};
param demand      {SPORTS};
param venue_order {VENUES} >= 0;

var y {VENUES} binary;
var x {SPORTS, VENUES, WEEKS} binary;
var w {SPORTS, WEEKS} binary;
var s {SPORTS, VENUES, WEEKS} >= 0;

minimize Total_Cost:
    sum {j in VENUES} cost[j] * y[j]
    - 10 * sum {i in SPORTS, j in VENUES, t in WEEKS} s[i,j,t];

subject to

one_week {i in SPORTS}:
    sum {t in WEEKS} w[i,t] = 1;

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