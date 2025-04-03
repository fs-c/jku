function generateFakeUUID() {
  return Math.random().toString(36).substring(2, 15);
}

function getRandomGenderOrNothing() {
  // 40% male, 40% female, 20% nothing
  const r = Math.random();
  if (r < 0.4) return "Male";
  if (r < 0.8) return "Female";
  return "";
}

function getRandomDate() {
  // Generate a random date between 1960 and 2024
  const start = new Date("1960-01-01").getTime();
  const end = new Date("2024-12-31").getTime();
  const randomTimestamp = start + Math.random() * (end - start);
  return new Date(randomTimestamp).toLocaleDateString("de-DE");
}

const cities = [
  "New York",
  "Los Angeles",
  "Chicago",
  "Houston",
  "Miami",
  "Philadelphia",
  "Phoenix",
  "San Antonio",
  "San Diego",
  "San Francisco",
  "Seattle",
  "Washington",
];

console.log("\\begin{longtable}{c l l c l}\\toprule");

console.log("\tAnonymized Name & Age & Gender & Date & City \\\\\\midrule");

for (let i = 0; i < 100; i++) {
  console.log(
    `\t${generateFakeUUID()} & ${Math.floor(
      Math.random() * 100
    )} & ${getRandomGenderOrNothing()} & ${getRandomDate()} & ${
      cities[Math.floor(Math.random() * cities.length)]
    } \\\\`
  );
}

console.log("\\bottomrule\\end{longtable}");
