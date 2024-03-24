t = 0:0.001:1;

f_1 = 1;
f_2 = 1/3;
phase_shift_1 = -0.2 * pi;
phase_shift_2 = -1/15 * pi;

original_1 = @(t) sin(2 * pi * f_1 * t);
time_delayed_1 = @(t) original_1(t - 0.1);
phase_shifted_1 = @(t) sin(2 * pi * f_1 * t + phase_shift_1);

original_2 = @(t) sin(2 * pi * f_2 * t);
time_delayed_2 = @(t) original_2(t - 0.1);
phase_shifted_2 = @(t) sin(2 * pi * f_2 * t + phase_shift_2);

figure();

ptd_1 = plot(t, time_delayed_1(t)); hold on;
pps_1 = plot(t, phase_shifted_1(t), "--"); hold on;
po_1 = plot(t, original_1(t)); hold off;
grid on;

legend([po_1, ptd_1, pps_1], 'original', 'time delayed', 'phase shifted');
xlabel('t');
ylabel('x_1(t), y_1(t)');

print -depsc ex3_1.eps

figure();

ptd_2 = plot(t, time_delayed_2(t)); hold on;
pps_2 = plot(t, phase_shifted_2(t), "--"); hold on;
po_2 = plot(t, original_2(t)); hold off;
grid on;

legend([po_2, ptd_2, pps_2], 'original', 'time delayed', 'phase shifted');
xlabel('t (s)')
ylabel('x_2(t), y_2(t)');

print -depsc ex3_2.eps
