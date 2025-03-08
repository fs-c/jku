```c
const int RED_PIN = 3;
const int YELLOW_PIN = 2;
const int GREEN_PIN = 1;

void setup() {
  pinMode(RED_PIN, OUTPUT);
  pinMode(YELLOW_PIN, OUTPUT);
  pinMode(GREEN_PIN, OUTPUT);
}

void loop() {
  // 1: red phase
  digitalWrite(RED_PIN, HIGH);
  digitalWrite(YELLOW_PIN, LOW);
  digitalWrite(GREEN_PIN, LOW);
  delay(15000);

  // 2: red & yellow phase
  digitalWrite(RED_PIN, HIGH);
  digitalWrite(YELLOW_PIN, HIGH);
  digitalWrite(GREEN_PIN, LOW);
  delay(3000);

  // 3: green phase
  digitalWrite(RED_PIN, LOW);
  digitalWrite(YELLOW_PIN, LOW);
  digitalWrite(GREEN_PIN, HIGH);
  delay(15000);

  // 3.1: green phase end
  for (int i = 0; i < 4; i++) {
    digitalWrite(GREEN_PIN, LOW);
    delay(500);
    digitalWrite(GREEN_PIN, HIGH);
    delay(500);
  }

  // 4: yellow phase
  digitalWrite(RED_PIN, LOW);
  digitalWrite(YELLOW_PIN, HIGH);
  digitalWrite(GREEN_PIN, LOW);
  delay(2000);
}
```
