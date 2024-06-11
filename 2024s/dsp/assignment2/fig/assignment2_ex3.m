function y = custom_conv(x, h)
    l_x = length(x);
    l_h = length(h);

    l_y = l_x + l_h - 1;

    y = zeros(1, l_y);

    % for every output element...
    for n = 1:l_y
        % (sum index) for every h index...
        for i = 0:l_h-1
            % make sure we don't have any out-of-bounds accesses
            if n - i > 0 && n - i <= l_x
                y(n) = y(n) + h(i + 1) * x(n - i);
            end
        end
    end
end

n = 0:49;
x = cos((2*pi/20) * n);

h = [0.25 0.5 0.25];

figure

stem(custom_conv(x, h));
xlabel('n');
ylabel('y[n]');

print -depsc ex3_1.eps

figure

p_custom_conv = stem(custom_conv(x, h)); hold on; grid on; box on;
p_builtin_conv = stem(conv(x, h), "--"); hold on; grid on; box on;

legend([p_custom_conv, p_builtin_conv], 'custom', 'built-in');
xlabel('n');
ylabel('y[n]');

print -depsc ex3_2.eps
