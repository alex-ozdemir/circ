void fa(int * c, int * d) {
    for (int i = 0; i < 2; i++) {
        d[i] = c[i];
    }
}

int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) {
    int c[2] = {a, b};
    int d[2] = {0, 0};
    // for (int i = 0; i < 2; i++) {
    //     c[i]++;
    // }
    fa(c, d);
    int sum = 0;
    for (int i = 0; i < 2; i++) {
        sum += d[i];
    }
    return sum;
}


// int fa(int a, int b, int c) {
//     return a + b + c + 1;
// }

// int fb(int a) {
//     return fa(a, a, a) + 2;
// }

// int fc(int a) {
//     return fb(a) + 3;
// }

// int main(__attribute__((private(0))) int a, __attribute__((private(1))) int b) {
//     int c = fc(a) + fc(b); 
//     return c;
// }
