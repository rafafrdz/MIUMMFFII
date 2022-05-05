var 1..3: bn; % n. banana cakes
var 1..7: ch; % n. chocolate cakes

% flour
constraint 250*bn + 200*ch <= 4000;
% bananas
constraint 2*bn  <= 6;
% sugar
constraint 75*bn + 150*ch <= 2000;
% butter
constraint 100*bn + 150*ch <= 500;
% cocoa
constraint 75*ch <= 500;

% maximize profit (converted to integers)
solve maximize 40*bn + 45*ch;