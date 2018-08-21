#include <stdio.h>

// assembly function that we are compiling
int entry_point();

int main() {
  printf("Result: %d\n", entry_point());
  return 0;
}
