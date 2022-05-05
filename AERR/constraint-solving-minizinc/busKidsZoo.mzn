var int : busCaro; var int: busBarato;

constraint busCaro >= 0;
constraint busBarato >= 0;
constraint 40 * busCaro + 30 * busBarato = 300;
solve minimize 500 * busCaro + 400 * busBarato;