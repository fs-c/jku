text = input('Enter text (space separated): ')

word_length_to_words: dict[int, list[str]] = dict()

for word in text.split(' '):
    word_length = len(word)
    if word_length not in word_length_to_words:
        word_length_to_words[word_length] = []
    word_length_to_words[word_length].append(word)

for length in sorted(word_length_to_words.keys()):
    words = word_length_to_words[length]
    print(f'length {length}: {len(words)} word{"s" if len(words) != 1 else ""} ({", ".join(words)})')
