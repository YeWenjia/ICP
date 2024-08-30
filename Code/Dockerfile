FROM node
WORKDIR /cp-compiler
COPY . .
RUN npm install
RUN npx spago build
CMD npm start
