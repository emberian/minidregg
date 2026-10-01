/* initbench: the start-up cost of libminidregg-channel.so as a member process pays it.
 * usage: initbench LIB.so  -> prints "dlopen_ms init_ms maxrss_kb" (one line).
 * dlopen + mdc_init only: the cost every relay / member / witness pays before its first tick. */
#include <dlfcn.h>
#include <stdio.h>
#include <sys/resource.h>
#include <time.h>
static double now_ms(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec * 1e3 + t.tv_nsec / 1e6; }
int main(int argc, char **argv) {
  if (argc != 2) { fprintf(stderr, "usage: initbench LIB.so\n"); return 2; }
  double t0 = now_ms();
  void *h = dlopen(argv[1], RTLD_NOW | RTLD_LOCAL);
  if (!h) { fprintf(stderr, "dlopen: %s\n", dlerror()); return 1; }
  double t1 = now_ms();
  int (*init)(void) = (int (*)(void))dlsym(h, "mdc_init");
  if (!init) { fprintf(stderr, "no mdc_init\n"); return 1; }
  if (init() != 0) { fprintf(stderr, "mdc_init failed\n"); return 1; }
  double t2 = now_ms();
  struct rusage ru; getrusage(RUSAGE_SELF, &ru);
  printf("%.1f %.1f %ld\n", t1 - t0, t2 - t1, ru.ru_maxrss);
  return 0;
}
