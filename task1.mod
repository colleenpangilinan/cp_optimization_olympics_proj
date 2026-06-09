set VENUES;
set SPORTS;
set WEEKS;

param cost        {VENUES};
param capacity    {VENUES};
param max_sports  {VENUES};
param eligible    {SPORTS, VENUES};
param demand      {SPORTS};
param sessions    {SPORTS};
param venue_order {VENUES} >= 0;

var y {VENUES} binary;
var x {SPORTS, VENUES} binary;


minimize Total_Cost:
    sum {j in VENUES} cost[j] * y[j];

subject to

assign_sport {i in SPORTS}:
    sum {j in VENUES} x[i,j] = 1;


eligibility {i in SPORTS, j in VENUES}:
    x[i,j] <= eligible[i,j] * y[j];

