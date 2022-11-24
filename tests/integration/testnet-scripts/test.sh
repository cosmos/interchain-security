#! /bin/bash
ISTRUE=$(echo '{"var":true}' | jq ".var")

if [  $ISTRUE == "true" ]; then
    echo "was matched to bool true"
else
    echo "matched someething else"
fi
