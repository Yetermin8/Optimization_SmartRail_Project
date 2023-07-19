#IEMS 313 Phase 2 Project
# Author: Max Rothfeder, Aidan Malcuso, Valentin De la Pena
# Date: 2 June 2023

# The set of stations. 
set stations;

#Set of Tracks
set tracks within (stations cross stations); 

#The set of shipments. 
set shipments; 

#The number of days in this shipment scheule
param T; 

#The set of days in the shipment schedule (starts on day 1, ends on day T)
set days = 1 .. T; 

# The origins, destinations, and volumes of the shipments.
param orig {shipments} within stations;
param dest {shipments} within stations;
param volume {shipments};

# The number of reloading zones at each station.
param num_reload {stations}; 

# The length of each track (in miles)
# Computed using distance formula based on the x and y coordinates
param x_coord {stations};
param y_coord {stations};
param len_track{(i,j) in tracks} := sqrt((x_coord[i]-x_coord[j])^2 + (y_coord[i]-y_coord[j])^2);

#The day that a shipments becomes abailable 
param avail_day{shipments};

#The day that a shipment is due for delivery
param deliv_day{shipments};

#Cost of shipping one container per mile (constant)
param cost_ship;

#Maximum number of cars per track per day in both directions, combined
param capa_track; 

#Maximum capacity of a single reload zone per day
param capa_reload; 

#The cost penalty for a container being late per day
param cost_penalty;

#The cost of building new track (per mile)
param cost_track;

#The cost of building a new reload zone
param cost_new_reload;

#The maximum number of reload zones
param max_reload; 

#The maximum number of tracks allowed
param max_tracks;


#DECISION VARIABLES

# The number of containers belonging to shipment s moving along track from station i to station j on day d. 
var x{s in shipments, d in days, (i,j) in tracks} integer >= 0;

# The number of containers belonging to shipment s moving along track from station j to station i on day d. 
var y{s in shipments, d in days, i in stations, j in stations: (j, i) in tracks} integer >= 0;

#NOTE: The use of X and Y ensures that there are containers can move in BOTH directions along a track

#Number of new reloading zones constructed at each staiton k 
var r{k in stations} integer, >=0; 

#Number of new tracks built along the track (i, j) - note, this will automatically add one on (j, i)
var t{(i, j) in tracks} integer,  >= 0; 

#Number of containers leaving from the origination station belonging to shipment s on day d
var ori{s in shipments, d in days} integer, >= 0; 

#Number of containers  belonging to shipment s DELIVERED to the destination station (for s) on day d
#Note: these are delivered containers, not arriving (they are delivered one day after arrival)
var del{s in shipments, d in days} integer, >= 0; 



#VARIABLES THAT MAKE UP OBJECTIVE FUNCTION

#The total shipping cost which equals the fixed cost of shipping per mile * the number of miles * the number
#of containers that move in both directions along a track
var total_ship_cost = sum {s in shipments, d in days, (i,j) in tracks} 
							cost_ship * len_track[i,j] * (x[s,d,i,j] + y[s, d, j, i]);
                      
# New track cost -> The number of new tracks built times the fixed cost of building a new track per mile
#times the length of the track built times the number of days (as fixed cost is amortized per day)                 
var new_track_cost = sum {(i, j) in tracks} (cost_track * len_track[i, j] * T * t[i, j]); 

# New reload cost -> The number of new reload stations built times the fixed cost of building a new reload station
#times the number of days (as fixed cost is amortized per day) 
var new_reload_cost = sum{k in stations} (cost_new_reload * T * r[k]); 

# Delay cost -> We only want to check containers that were late (i.e. when the day is after the delivery day)
#Then, we multiply the cost penalty per day late * number of days late * # containers delivered on that day
#We only include d > deliv_day as d = deliv_day would just add 0 (those are on time)

var delay_cost = sum{s in shipments, d in days: d > deliv_day[s]}
						cost_penalty * (d - deliv_day[s]) * del[s, d]; 


#OBJECTIVE FUNCTION 
# We aim to minimize the total cost of shipping the containers within the network for our customers
#That include total_ship_cost + new_track_cost + new_reload_cost + delay_cost; 

minimize total_cost:
	total_ship_cost + new_track_cost + new_reload_cost + delay_cost;
	
	
#CONSTRAINTS

# 1) Flow balance on day d = 1
# For each shipment s and each station k on each day d, The number of containers leaving a station k (on all tracks leaving k)
#must equal the number of containers originating from that station k (assuming k is the origin station)

#On day 1, nothing can be delivered and nothing can have arrived from the previous day
#We note that on the right side, we flip (k, j) to (j, k) as we go through tracks to get the reverse direction, 
#Then we want ones that originate at node k and go to node j!!

subject to flow_balanceI {s in shipments, k in stations}: 
    if orig[s] == k then ori[s,1] = sum{(k,j) in tracks} x[s, 1, k, j] + 
    								sum{(j,k) in tracks} y[s, 1, k, j];  

# 2) Flow balance on days 2 .. T (in this instance, T = 14)
# For each shipment s and each station k on each day d, the number of containers entering station k (on the previous day d-1) 
# added to the of containers originating from station k on day d (assuming k is the origin station for shipment s) 
# must equal 
# The number of containers leaving the station k on day d (accross all tracks leaving k) plus the number of containers
# being delivered on the current day d (assuming k is the destination station for shipment s)
# Note: with this formulation, a we use current day for delivery as the contaienr must have arrived yesterday (d-1)

subject to flow_balanceII {s in shipments, k in stations, d in 2 .. T }: 
    sum {(i,k) in tracks} x[s, (d-1), i,k] + sum {(k,i) in tracks} y[s, (d-1), i,k] + 
    (if orig[s] == k then ori[s,d])
     =  
    sum {(k,j) in tracks} x[s, d, k,j] + sum {(j,k) in tracks} y[s, d, k,j] + 
    (if dest[s] == k then del[s, d]);
    
# 3) Origination Policy      
#For each shipment s, the total number of containers leaving the origin node on the 
#available day to the second to last day must equal the total volume for that shipment 
#(We note that it could be the case that no container can originate on T-2 based on track layout, but that is case dependent)
# No matter what, a container cannot leave on the last day T as all containers must be DELIVERED on or before T

subject to origination {s in shipments}: 
	sum{d in avail_day[s] .. (T-1)} ori[s, d] = volume[s]; 
	

# 4) Delivery Policy 
# For each shipment s, the total number of containers delivered to the destination node from the day after the
#available day to the final day T must equal the total volume for that shipment. 
# We note that it could be the case that based on the track layout, a container cannot every be delivered for a specific shipment
#the day after it's available for pickup. However, no container can Ever be delivered on the available date
subject to destination {s in shipments}: 
	sum{d in (avail_day[s] + 1) .. T} del[s, d] = volume[s];

# 5) No shipping before available 
# For each shipment, track, and day (where the day is before the available day), NO containers can be shipped along a track (i, j)
# In either direction
# For simplicity, we combine both directions as they must be positive so if their sum is 0, both are also 0!
subject to availibility {s in shipments, (i, j) in tracks, d in days: d < avail_day[s]}:
	x[s, d, i, j] + y[s, d, j, i] = 0;
	
#Alternatively, we could say that the sum or originating containers from day 0 .. (aviail_day[s] -1) + day T = 0
#AND, the sum of containers being delivered from day 1 ... avail_day[s] = 0. This has the exact same effect as 
#preventing any shipping prior to the day of availibility!! However, our team believes the formulation above
#is more intuitive/clear in its meaning!!
	
	
# 6) For each station and day, the number of containers arriving to a station k can NOT exceed reloading capacity 
# Note: Reloading capacity is now dependent on the number of new reloading r[k] stations built. Capa_reload is a constant
#value for EACH reloading zone, and they start with num_reload[k]

subject to reload_capa_limit {k in stations, d in days}:
    sum {s in shipments, (i,k) in tracks} x[s, d, i,k] + 
    sum {s in shipments, (k,i) in tracks} y[s, d, i,k]
     <= capa_reload * (r[k] + num_reload[k]);
    

# 7) For each track (i, j) on each day d, the number of containers moved along track (i, j) in EITHER DIRECTION 
# should NOT exceed track capacity (hence the sum of x and y decision variables). 
#We note that capa_track is a constant value, there is 1 track to begind a t[i, j] new ones built!
subject to track_capa_limit {(i,j) in tracks, d in days}:
    sum{s in shipments} (x[s,d, i,j] + y[s, d,j,i]) <= capa_track *( 1 + t[i, j]);


#8) There can be at most max_tracks (including the original one track) for each route (i, j)
#In this instance, that is a maximum of 4 tracks. 
subject to max_num_tracks {(i, j) in tracks}: 
	(1 + t[i, j]) <= max_tracks; 
	
#9) There can be at most max_reload zones at each station k
#In this instance, that is a maximum of 12 reload zones 
subject to max_reload_zones {k in stations}: 
	num_reload[k] + r[k] <= max_reload; 

	
	



