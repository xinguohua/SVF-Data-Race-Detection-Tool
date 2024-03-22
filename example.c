#include <stdlib.h>
#include <stdio.h>
#include <pthread.h>

// basic data race example
int x = 0;

void *increment(void *threadid) {
    for (int i = 0; i < 100000000; i++) {
        x++;
    }
    return NULL;
}

void *decrement(void *threadid) {
    for (int i = 0; i < 100000000; i++) {
        x--;
    }
    return NULL;
}

int main() {
    pthread_t threads[2]; //using just two threads
    pthread_attr_t attr;
    void *status;

    // initialise and set thread joinable
    pthread_attr_init(&attr);
    pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_JOINABLE);

    pthread_create(&threads[0], NULL, increment, (void *)1);
    pthread_create(&threads[1], NULL, decrement, (void *)2);
    pthread_join(threads[0], &status);
    pthread_join(threads[1], &status);

    printf("%d\n", x);

    return 0;
}