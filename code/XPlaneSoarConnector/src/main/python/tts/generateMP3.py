from gtts import gTTS
import sys

if len(sys.argv) > 3:
    print("Bad args.")
    exit(1)

elif len(sys.argv) < 3:
    txt = raw_input("Text:")
    filename = txt.replace(" ", "_")[:10] + ".mp3"

else:
    txt = sys.argv[1]
    filename = sys.argv[2]

f = open(filename, 'w+b')
tts = gTTS(text=txt, lang='en')
tts.save(filename)
f.close()
