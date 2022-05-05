var 0..100 : busCaro;
var 0..100: busBarato;

constraint 40 * busCaro + 30 * busBarato = 300;
solve minimize 500 * busCaro + 400 * busBarato;