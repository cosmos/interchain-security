// -*- mode: Bluespec; -*-
// A simple module for time that makes timings more readable,
// e.g. 5 * Minute.
// The base unit are seconds, i.e. to get the number of seconds in a time value, just treat it as an int.
module Time {
    type Time = int

    pure val Second = 1    
    pure val Minute = 60 * Second
    pure val Hour = 60 * Minute
    pure val Day = 24 * Hour
    pure val Week = 7 * Day
    pure val Year = 365 * Day
}