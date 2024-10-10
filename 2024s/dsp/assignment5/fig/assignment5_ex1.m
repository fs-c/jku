clear; close all; clc;

load("filter_coefficients.mat");

i = 1:4;
n = 0:800;

x = sum((1./(2*i - 1)) .* sin(2 * pi * 0.005 * (2 * i - 1) .* n'), 2);

tiledlayout("horizontal")

nexttile
plot(n, x)

nexttile
plot(n, filter(b1, a1, x))

nexttile
plot(n, filter(b2, a2, x))

set(gcf, 'Position',  [100, 100, 1250, 400])

print -depsc ex1_1.eps
