fs = 100000;
t = 0:1/fs:0.002;

f1 = 4000;
f2 = 6000;

x = sin(2*pi*f1*t) + sin(2*pi*f2*t)

sampledT = t(1:10:end)
sampledX = x(1:10:end)

figure();

plot(t, x); hold on;
stem(sampledT, sampledX); hold off;
xlabel('Time (s)');
ylabel('Amplitude');
grid on;

print -depsc ex1_3.eps
