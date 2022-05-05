#include <stdio.h>
#include <stdbool.h>
#include <stdlib.h>
#include <time.h>
#include <assert.h>

bool f1(int x, int y) {
  return x - y > 0;
}

bool f2(int x, int y) {
  return x > y;
}

int generate_random();

const int NUM_TESTS = 1000;

int main(void) {
  srand(time(NULL));
  
  for (int i = 0; i < NUM_TESTS; i++) {
    int x = generate_random();
    int y = generate_random();
    
    printf("x = %15d, y = %15d, x - y = %15d\n", x, y, x - y);
        
    assert(f1(x, y) == f2(x, y));
  }
  
  return 0;
}

int generate_random() {
  int sign = rand() % 2;
  if (sign == 0) sign = -1;
  return rand() * sign;
}