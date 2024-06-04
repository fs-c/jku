clear; close all; clc;

[audioSignal, fs] = audioread('dtmf.wav');

%%

segmentDuration = 0.3;
numSamples = round(segmentDuration * fs);
segment = audioSignal(1:numSamples);
t = (0:numSamples-1) / fs;

figure;
plot(t, segment);
xlabel('Time (s)');
ylabel('Amplitude');
grid on;

print -depsc ex4_1.eps

%%

n = length(audioSignal);
spectrum = fft(audioSignal);

doubleSidedSpectrum = abs(spectrum / n);
singleSidedSpectrum = doubleSidedSpectrum(1:floor(n / 2) + 1);
singleSidedSpectrum(2:end - 1) = 2 * singleSidedSpectrum(2:end - 1);

f = fs / n * (0:floor(n / 2));
cutoff = f <= 2000; % cut off freqs above 2k Hz (they don't contain information anyways)

figure;
plot(f(cutoff), singleSidedSpectrum(cutoff));
xlabel('Frequency (Hz)');
ylabel('Magnitude');
grid on;

print -depsc ex4_2.eps

%%

% we do some wacky shit to cut off freqs above 2kHz here, but it works

segmentLength = 256;
overlapLength = 128;
stepSize = segmentLength - overlapLength;

n = length(audioSignal);
numSegments = floor(n / stepSize);

spectogram = zeros(segmentLength, numSegments);

% hamming returns a 1xN matrix but our signal parts will be Nx1 matrices,
% so we transpose early
window = hamming(segmentLength)';

for i = 1:numSegments
    startIndex = (i - 1) * stepSize + 1;
    endIndex = startIndex + segmentLength - 1;

    % get the part of the audio signal to be processed
    signalPart = zeros(1, segmentLength);
    if endIndex <= n
        signalPart(1:end) = audioSignal(startIndex:endIndex);
    else
        signalPart(1:end) = audioSignal(startIndex, end);
    end

    % apply our window
    signalPart = signalPart .* window;

    % get the spectrum, cut off the upper half
    spectrumPart = abs(fft(signalPart, segmentLength * 2));
    spectogram(:, i) = spectrumPart(1:end/2);
end

% divide everything by two here since we want to show only the lower half
% of the frequencies
frequencies = linspace(0, fs / 4, segmentLength / 2);

times = linspace(0, n / fs, numSegments);

figure,
xlabel('Time (s)'),
ylabel('Frequency (Hz)'),
surface(times, frequencies, spectogram(1:segmentLength / 2, :)),
colorbar;

print -depsc ex4_3.eps

%%

segmentLength = 256;
overlapLength = 128;
stepSize = segmentLength - overlapLength;

n = length(audioSignal);
numSegments = floor(n / stepSize);

spectogram = zeros(segmentLength, numSegments);

for i = 1:numSegments
    startIndex = (i - 1) * stepSize + 1;
    endIndex = startIndex + segmentLength - 1;

    % get the part of the audio signal to be processed
    signalPart = zeros(1, segmentLength);
    if endIndex <= n
        signalPart(1:end) = audioSignal(startIndex:endIndex);
    else
        signalPart(1:end) = audioSignal(startIndex, end);
    end

    % get the spectrum, cut off the upper half
    spectrumPart = abs(fft(signalPart, segmentLength * 2));
    spectogram(:, i) = spectrumPart(1:end/2);
end

frequencies = linspace(0, fs / 4, segmentLength / 2);
times = linspace(0, n / fs, numSegments);

figure,
xlabel('Time (s)'),
ylabel('Frequency (Hz)'),
surface(times, frequencies, spectogram(1:segmentLength / 2, :)),
colorbar;

print -depsc ex4_4.eps
