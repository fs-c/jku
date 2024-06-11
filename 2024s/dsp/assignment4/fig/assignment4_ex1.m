t = 0:1e-6:1e-3;
x = 1 + 0.5 * cos(2 * pi * 2000 * t) + 2 * sin(2 * pi * 4000 * t) + sin(2 * pi * 6000 * t);

plot(t, x); hold on;
xlabel('t');
ylabel('x(t)');
grid on;

print -depsc ex1_1.eps
