clear; close all; clc;

img = imread('pavian.png'); % Choose any picture you like here
img = rgb2gray(img);

%% Display image
figure; subplot(321);
imshow(img);
title('Ausgangsbild');

%% FFT
fft2d = fft2(img);

% Display the FFT image.
subplot(322);
imshow(log(fftshift(abs(fft2d))), []);
title('2D-FFT');

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% 
%Your turn

[n, m] = size(fft2d);

% create centered grid of indexes
[x, y] = meshgrid(1:m, 1:n);
x = x - floor(m / 2);
y = y - floor(n / 2);

% for every cell, get its distance from the center
distance = sqrt(x.^2 + y.^2);

% simple hard-cutoff bandpass filter
inner_cutoff = 20;
outer_cutoff = 60;
bandpass = double(distance >= inner_cutoff & distance <= outer_cutoff);

subplot(323);
imshow(bandpass, []);
title('Bandpass Filter');

% shift and filter
img_filtered = fftshift(fft2d) .* bandpass;

subplot(324);
imshow(abs(img_filtered), []);
title('Filtered 2D-FFT');

% unshift
img_filtered = ifftshift(img_filtered);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% IFFT to obtain filtered image
img_filtered = ifft2(img_filtered);
subplot(325);
imshow(real(img_filtered), []);
title('Gefiltertes Ausgangssignal');

print -depsc ex3_1.eps
