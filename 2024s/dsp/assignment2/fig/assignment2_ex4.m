function X = dtft(x, n, w)
    X = x * exp(-1j * w .* n');
end

n = -10:11;
x = (0.8).^abs(n);

w = -pi:0.001:pi;
X = dtft(x, n, w);

f = figure;
f.Position = [100 100 1400 600];

subplot(211); hold on; grid on; box on;
plot(w, abs(X));
xlabel('\Omega');
ylabel('|X(e^{j \Omega})|')

subplot(212); hold on; grid on; box on;
plot(w, angle(X));
xlabel('\Omega');
ylabel('angle(X(e^{j \Omega}))');

print -depsc ex4_1.eps

w = (4 * -pi):0.001:(4 * pi);
X = dtft(x, n, w);

f = figure;
f.Position = [100 100 1400 600];

subplot(211); hold on; grid on; box on;
plot(w, abs(X));
xlabel('\Omega');
ylabel('|X(e^{j \Omega})|')

subplot(212); hold on; grid on; box on;
plot(w, angle(X));
xlabel('\Omega');
ylabel('angle(X(e^{j \Omega}))');

print -depsc ex4_2.eps
