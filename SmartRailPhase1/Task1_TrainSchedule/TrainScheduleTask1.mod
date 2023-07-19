#Train Scheduling Project - Task 1
#10 May 2023
# Max Rothfeder, Aidan Macaluso, Valentin de la Pena, Yetayal Tizale

#Set of Stations = ; 
set stations; 

#Set of Tracks
set tracks within (stations cross stations); 

#Set of Shipments; 
set shipments; 


#Constant Parameters 

#Cost of shipping one container per mile (constant)
param cost_ship;

#Maximum number of cars per track per day in both directions, combined
param capa_track; 

#Maximum capacity of a single reload zone per day
param capa_reload; 

#Cost for reloading one container in a reload zone
param cost_reload;


#Paramters that depend on other items

#The origin station for a given shipment 
param orig{shipments};

#The destination station for a given shipment
param dest{shipments};

#The total number of containers that need to be moved for a given shipment
param volume{shipments};

#The number of reloading zones available at a station
param num_reload{stations}; 

#The x_coordinate for a given station
param x_coord{stations};

#The y_coordinate for a given station 
param y_coord{stations};


#DECISION VARIABLES
#The number of containers belonging to shipment s going from station i to station j
var x{shipments, tracks} >= 0,  integer;

#Note: The combination of all the different decision varaibles for a single shipment will give the 
#path from the origin to the final destination
#Note 2: All decision variables (i.e. number of containers) must be integers and nonnegative 

#OBJECTIVE FUNCTION!!

#The objective function is minimizing the total costs made up of two components
#1) For each shipment and track, the length of the track times the cost per mile times the 
#number of containers that go on that route
#2) For each shipment and track, the cost of reloading a container times the number of 
# containers that go on the route from station i to j
# Note: since we reload every time a container finishes one segment (incuding final), all 
# we need to do is use the x[s, i, j] decision variable. This will automatically ignore 
# The start as there is no track for the starting location!!

minimize costs: 
    sum{s in shipments, (i,j) in tracks} 
    sqrt((x_coord[j]-x_coord[i])^2 + (y_coord[j] -y_coord[i])^2 )*
    cost_ship * x[s, i, j]
	+ sum{s in shipments, (i,j) in tracks} cost_reload*x[s, i, j];
	
#CONSTRAINTS

#The first constraint is to ensure the reload limit is not exceeded at any station
subject to reload_limit {k in stations}:
	sum{s in shipments, (i,k) in tracks} x[s, i, k] <= capa_reload * num_reload[k];
	
#The second constraint is to ensure that the track capacity is not exceeded (in both directions combined)
subject to track_lim {(i, j) in tracks}:
	sum{s in shipments} (x[s, i, j] + x[s, j, i]) <= capa_track; 
	
#The third constraint is the flow balance constraint!!

#The total amount going into a node minus the total amount going out of a node
#Must be equal to the number of containers that should end in a node minus the number of containers
#That start in a node. This must be true for EACH SHIPMENT!!!. 

subject to balance_limit {k in stations, s in shipments}: 
	   sum{(i, k) in tracks} x[s, i, k] 
     - sum{(k, j) in tracks} x[s, k, j]
   = - (if orig[s] == k then volume[s] else 0) + 
	   (if dest[s] == k then volume[s] else 0);
	      
	      
	      
	      
	      
	      
	      
	      


	   
	 