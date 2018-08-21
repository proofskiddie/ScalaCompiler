#include <stdio.h>
#include <stdlib.h>

// assembly function that we are compiling
int entry_point(char* heap);

int main() {
  char* heap = malloc(10000 * 8);
  printf("Exit Code: %d\n", entry_point(heap));
  free(heap);
  return 0;
}
