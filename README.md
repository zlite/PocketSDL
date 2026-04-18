![screenshot](screenshot.png)
This is a minimal self-driving lab demonstration to "discover" color theory by doing an exploration/exploitation search of color space by driving a RGB LED and measuring it with a color sensor. 

Load code onto ESP32 with the Platormio extension in VSCode (change the port in the ini file to whatever your ESP32 shows up as). Codex or Claude Code extensions in VS Code will do this for you. If you haven't set your wifi details in the code, it will prompt you to enter them on the serial terminal (115200 baud) and then save them so you don't have to do it again. 

Alternatively, you can just load the file on the ESP32 using the Arduino IDE.

![insides](insides.jpg)
----
![flashing](animation.gif)

BOM:
- [Adafruit Feather ESP32 V2](https://www.adafruit.com/product/5400)
- [Adafruit 10-channel color sensor](https://www.adafruit.com/product/4698)
