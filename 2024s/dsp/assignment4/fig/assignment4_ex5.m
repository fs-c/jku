clear; close all; clc;

N = 128;
n = 0:N-1;
w1 = 2*pi*0.1;
w2 = 2*pi*0.15;
x = cos(w1*n) + cos(w2*n);

%%

figure,
stem(abs(fft(x))),
xlabel('Frequency (Hz)'),
ylabel('Magnitude'),
grid on;

print -depsc ex5_1.eps

%%

window = hamming(N)';

y = x .* window;

figure,
stem(abs(fft(y))),
xlabel('Frequency (Hz)'),
ylabel('Magnitude'),
grid on;

print -depsc ex5_2.eps

%%

N = 128;
n = 0:N-1;
w1 = pi;
w2 = 2 * pi;
x = cos(w1*n) + cos(w2*n);

figure,
stem(abs(fft(x))),
xlabel('Frequency (Hz)'),
ylabel('Magnitude'),
grid on;

print -depsc ex5_3.eps
