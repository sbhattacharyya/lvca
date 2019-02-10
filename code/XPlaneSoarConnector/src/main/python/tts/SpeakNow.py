from gtts import gTTS
from pygame import mixer
import pygame
from tempfile import mkstemp
import sys

argc = len(sys.argv)

if argc < 2:
    txt = raw_input("Text:")

else:
    txt = sys.argv[1]

mixer.init()
pygame.init()
mixer.music.set_endevent(1)
tempFileName = mkstemp()[1]

f = open(tempFileName, 'w+b')
tts = gTTS(text=txt, lang='en')
tts.save(tempFileName)
mixer.music.load(f)
mixer.music.play()
pygame.event.wait()
f.close()
