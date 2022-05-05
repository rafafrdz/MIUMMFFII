%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Rafael Fernandez Ortiz
%% AERR - Assignment Depot
%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%

include "alldifferent.mzn" ;
int: PSize;
% For instance:
% int: PSize = 4;
int: TSize = (PSize +1 ) * 2 ;
var 1..TSize: Depot;
int: TourLength = PSize+1 ;

int: AWH = 1 ;
int: BWH = TourLength + 1;

int: ASize = TourLength + 1;
int: BSize = TourLength + 1;

% Tour for truck A
array[1..ASize] of var 1..TSize: TourA ;
% Tour for truck B
array[1..BSize] of var 1..TSize: TourB ;

array[1..14, 1..14] of int: AllDist;
% For instance
% array[1..14, 1..14] of int: AllDist =
% [|0,  20,  24,  33,  33,  43,  56,  63,  61,  71,  79,  86,  94,  102
% |20,  0,  18,  34,  43,  50,  66,  72,  68,  79,  86,  93,  100,  108
% |24,  18,  0,  16,  28,  34,  50,  55,  50,  62,  68,  75,  82,  90
% |33,  34,  16,  0,  16,  19,  34,  40,  34,  46,  52,  59,  66,  74
% |33,  43,  28,  16,  0,  10,  23,  30,  28,  38,  46,  53,  61,  69
% |43,  50,  34,  19,  10,  0,  16,  22,  18,  29,  36,  44,  51,  59
% |56,  66,  50,  34,  23,  16,  0,  8,  11,  16,  24,  32,  40,  48
% |63,  72,  55,  40,  30,  22,  8,  0,  8,  8,  16,  24,  32,  40
% |61,  68,  50,  34,  28,  18,  11,  8,  0,  11,  18,  25,  33,  41
% |71,  79,  62,  46,  38,  29,  16,  8,  11,  0,  8,  16,  24,  32
% |79,  86,  68,  52,  46,  36,  24,  16,  18,  8,  0,  8,  16,  24
% |86,  93,  75,  59,  53,  44,  32,  24,  25,  16,  8,  0,  8,  16
% |94,  100,  82,  66,  61,  51,  40,  32,  33,  24,  16,  8,  0,  8
% |102,  108,  90,  74,  69,  59,  48,  40,  41,  32,  24,  16,  8,  0
% |] ;

int: MaxDist = sum([max([AllDist[N,M] |M in 1..TSize]) | N in 1..TSize]) ;
int: MaxLeg = max([max([AllDist[N,M] | M in 1..TSize]) | N in 1..TSize]) ;

array[1..ASize] of var 0..MaxLeg: ALegDist ;
array[1..BSize] of var 0..MaxLeg: BLegDist ;

var 0..MaxDist: ADist;
var 0..MaxDist: BDist;
var 0..MaxDist: Solution;


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Constraints
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Optimized variable
constraint ADist = sum(ALegDist) ;
constraint BDist = sum(BLegDist) ;
constraint Solution = max(ADist,BDist) ;

% The distance between the Nth and (N+1)th locations.
constraint forall (N in 1..ASize-1) (ALegDist[N] = AllDist[TourA[N], TourA[N+1]]);

% The distance from the final location back to the warehouse.
constraint ALegDist[ASize] = AllDist[TourA[ASize],TourA[1]] ;  
constraint forall (C in 1..BSize-1) (BLegDist[C] = AllDist[TourB[C], TourB[C+1]]);
constraint BLegDist[BSize] = AllDist[TourB[BSize],TourB[1]] ; 

% Ensure all location are visited by at least one of the tours A or B.
constraint forall (C in 1..TSize) ( exists (Y in TourA++TourB) (Y = C) );

% Ensure each tour visits different locations.
constraint alldifferent([TourA[N]|N in 2..ASize]);
constraint alldifferent([TourB[N]|N in 2..BSize]);

% The WH must be visited first
constraint TourA[1] = AWH ;
constraint TourB[1] = BWH ;

% Don't come back to the WH until the deliveries are done
constraint forall (N in 3..ASize-1) (TourA[N] != AWH);
constraint forall (N in 3..BSize-1) (TourB[N] != BWH);

constraint symmetry_breaking_constraint( TourA[ASize] != AWH );
constraint symmetry_breaking_constraint( TourA[BSize] != BWH );

% WH cannot be visit by different trucks
constraint forall (N in 1..ASize) (TourA[N] != BWH);
constraint forall (N in 1..BSize) (TourB[N] != AWH);

% Depot constraints
constraint forall (N in 1..ASize) ( (TourA[N] > TourLength /\ TourA[N] != Depot ) -> ( exists (M in 1..N-1) (TourA[M] = Depot) ) );
constraint forall (N in 1..BSize) ( (TourB[N] <= TourLength /\ TourB[N] != Depot ) -> ( exists (M in 1..N-1) (TourB[M] = Depot) ) ) ;
          
% Solve

solve 
    :: seq_search([
        int_search(TourA ++ TourB, first_fail, indomain_min, complete),
        int_search([Depot], input_order, indomain_min, complete)
    ])
    minimize Solution;
    
% Output

output[ "%% ######################################## ",
       ";\nMaximum Tour Distance: ", show(Solution), 
       ";\nDepot = ", show(Depot), 
       ";\nADist is: ",show(ADist), 
       ";\nBDist is: ", show(BDist),       
       ";\nTourA = ",  show(TourA), 
       ";\nTourB = ", show(TourB), 
       ";\nSolution = ", show(Solution),
       ";\n%% ######################################## "] ;