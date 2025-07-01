import { Effect, Console } from "effect";

const program = Console.log("hello effect world!");

Effect.runSync(program);
