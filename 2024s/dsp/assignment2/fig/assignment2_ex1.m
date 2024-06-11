clear
close all
clc 

function result = discreteDirac(n)
    result = (n == 0);
end

function result = customPower(period)
    result = (1 / length(period)) * sum(power(abs(period), 2));
end

function result = energy(signal)
    result = sum(power(abs(signal), 2));
end

n12 = -5:10;
x1 = -4 * discreteDirac(n12 + 3) + 4 * discreteDirac(n12) - discreteDirac(n12 - 3) + 2 * discreteDirac(n12 - 7);
x2 = exp(-0.31 * n12);

n34 = 0:256;
x3 = 3 * sin(2 * pi * (3.5 / 64) * n34);
x4 = -cos((9 / 64) * n34);

customPower(x3(1:128))

energy(x1)
energy(x2)
energy(x3)
energy(x4)

% Visualization
f = figure;
f.Position = [100 100 1400 600];

subplot(121); hold on; grid on; box on;
stem(n12, x1);
stem(n12, x2);
xlabel('n');
ylabel('x_1[n], x_2[n]');

subplot(122); hold on; grid on; box on;
plot(n34, x3);
plot(n34, x4);
xlabel('n');
ylabel('x_3[n], x_4[n]');

print -depsc ex1_1.eps
